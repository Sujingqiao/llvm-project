/**
 * 🧠 模拟现代 Polly 模块工作流程（基于 llvm-project 主线）
 * 
 * 注意：这是“可读性优先”的伪代码，不保证编译，但接口尽量贴近真实。
 * 
 * 核心变化：
 *   - 使用 LLVM PassManager 框架
 *   - ScopDetection → 作为 Analysis
 *   - ScopBuilder → 在 Pass 中构建
 *   - 依赖和调度 → 通过 isl 自动完成
 *   - Codegen → 通过 Polly 的 codegen Pass
 */

#include "polly/Analysis/ScopDetection.h"
#include "polly/Analysis/ScopInfo.h"
#include "polly/Analysis/DependenceInfo.h"
#include "polly/Transform/ScopToScopPass.h"
#include "polly/Transform/CodeGeneration.h"

#include "mlir/Conversion/LLVMCommon/TypeConverter.h"
#include "isl/ctx.h"
#include "isl/set.h"
#include "isl/map.h"
#include "isl/union_map.h"
#include "isl/schedule.h"
#include "isl/ast.h"

// 使用 LLVM 前向声明
namespace llvm {
class Function;
class Module;
class PassBuilder;
} // namespace llvm

// 使用 Polly 前向声明
namespace polly {
class Scop;                    // 多面体模型核心
class ScopDetectionWrapperPass; // SCoP 检测分析
class ScopInfo;                 // SCoP 建模
class DependenceInfo;           // 依赖分析
class CodeGenPass;              // 代码生成
} // namespace polly

using namespace llvm;
using namespace polly;

/**
 * 🎯 Step 1: SCoP 检测（Analysis）
 * 
 * 思路：
 *   Polly 首先分析函数，判断哪些循环区域可以被建模为 SCoP。
 *   这是一个 Analysis Pass，供其他 Pass 使用。
 */
struct ScopDetectionPass : public AnalysisInfoMixin<ScopDetectionPass> {
  using Result = std::optional<ScopDetectionResult>;

  Result run(Function &F, FunctionAnalysisManager &FAM) {
    // 检查函数是否可以被建模
    if (!isEligibleForScop(F)) {
      return std::nullopt;
    }

    // 遍历循环
    LoopInfo &LI = FAM.getResult<LoopAnalysis>(F);
    for (auto *L : LI) {
      if (isAffineLoop(L)) {  // 边界和访问是仿射的
        ScopDetectionResult Result;
        Result.addLoop(L);
        return Result;
      }
    }

    return std::nullopt;
  }

private:
  static AnalysisKey Key;
  friend struct AnalysisInfoMixin<ScopDetectionPass>;
};

/**
 * 🎯 Step 2: 构建 SCoP 模型（ScopInfo）
 * 
 * 思路：
 *   在 Pass 中，使用 ScopDetection 的结果，构建完整的多面体模型：
 *     - 语句域（Domains）
 *     - 访问关系（Accesses）
 *     - 参数（Parameters）
 *   这个过程叫 "Scop Construction"
 */
struct BuildScopPass : public PassInfoMixin<BuildScopPass> {
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &FAM) {
    // 获取 SCoP 检测结果
    auto ScopDetect = FAM.getResult<ScopDetectionPass>(F);
    if (!ScopDetect)
      return PreservedAnalyses::all();

    // 创建 SCoP 对象
    std::unique_ptr<Scop> S = std::make_unique<Scop>(&F);

    // 设置上下文（isl_ctx）
    isl_ctx *Ctx = isl_union_set_get_ctx(S->getDomain().get());

    // 遍历检测到的循环结构
    for (auto *L : ScopDetect->getLoops()) {
      // 提取循环边界：例如 {i : 0 <= i < N}
      isl_set *LoopDomain = extractLoopDomain(L, Ctx);
      S->addDomain(LoopDomain);

      // 提取语句和访问
      for (auto &BB : L->getBlocks()) {
        for (auto &I : *BB) {
          if (isa<StoreInst>(&I) || isa<LoadInst>(&I)) {
            // 构建访问映射：例如 [i,j] -> A[i][j]
            isl_map *AccessMap = buildAccessMap(&I, Ctx);
            MemoryAccess::AccessType Type = 
                isa<StoreInst>(&I) ? MemoryAccess::WRITE : MemoryAccess::READ;
            S->addAccess(std::make_unique<MemoryAccess>(AccessMap, Type));
          }
        }
      }
    }

    // 👉 此时 S 是一个完整的多面体模型
    //    可用于后续分析和优化

    // 将 SCoP 存入模块或函数属性，供后续 Pass 使用
    F.setMetadata("polly.scop", S->getAsMDNode(F.getContext()));

    return PreservedAnalyses::none();
  }
};

/**
 * 🎯 Step 3: 依赖分析（DependenceInfo）
 * 
 * 思路：
 *   使用 isl 计算 RAW/WAW/WAR 依赖。
 *   Polly 提供 DependenceInfo Analysis。
 */
struct DependenceAnalysisPass : public AnalysisInfoMixin<DependenceAnalysisPass> {
  using Result = DependenceInfo;

  Result run(Function &F, FunctionAnalysisManager &FAM) {
    // 获取 SCoP
    auto *S = getScopFromMetadata(F);
    if (!S) return DependenceInfo();

    // 使用 isl 计算依赖
    isl_union_map *Dependences = isl_union_map_empty(isl_space_set_alloc(Ctx, 2, 0));

    // RAW 依赖：读不能早于写
    isl_union_map *RAW = isl_dependence_from_scop(S->getIslScop(), 
                                                  ISL_DEPENDENCE_RAW);
    Dependences = isl_union_map_union(Dependences, RAW);

    // WAW 依赖
    isl_union_map *WAW = isl_dependence_from_scop(S->getIslScop(), 
                                                  ISL_DEPENDENCE_WAW);
    Dependences = isl_union_map_union(Dependences, WAW);

    // WAR 依赖
    isl_union_map *WAR = isl_dependence_from_scop(S->getIslScop(), 
                                                  ISL_DEPENDENCE_WAR);
    Dependences = isl_union_map_union(Dependences, WAR);

    return DependenceInfo(Dependences);
  }

private:
  static AnalysisKey Key;
  friend struct AnalysisInfoMixin<DependenceAnalysisPass>;
};

/**
 * 🎯 Step 4: 调度优化（通过 isl 自动完成）
 * 
 * 思路：
 *   Polly 不再手动构造 schedule tree，
 *   而是调用 isl 的调度器自动搜索最优调度。
 *   例如：tiling, interchange, parallelization.
 */
struct OptimizeSchedulePass : public PassInfoMixin<OptimizeSchedulePass> {
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &FAM) {
    auto *S = getScopFromMetadata(F);
    if (!S) return PreservedAnalyses::all();

    isl_ctx *Ctx = S->getIslCtx();

    // 1. 获取当前调度（初始为循环顺序）
    isl_schedule *Current = S->getSchedule();

    // 2. 调用 isl 的调度器进行优化
    //    例如：尝试最大化局部性（tiling）
    isl_options_set_schedule_algorithm(Ctx, ISL_SCHEDULE_ALGORITHM_ISL);
    
    // 让 isl 自动决定是否 tiling、如何 tiling
    isl_schedule *Optimized = isl_schedule_from_domain_and_dependences(
        S->getDomain(),           // 语句域
        S->getDependences(),      // 依赖关系
        isl_union_map_empty(isl_space_set_alloc(Ctx, 0, 0)) // 无上下文约束
    );

    // 3. 设置新调度
    S->setSchedule(Optimized);

    // 👉 isl 内部会：
    //    - 分析依赖
    //    - 搜索合法调度
    //    - 应用 tiling、fusion 等变换
    //    - 返回 schedule tree

    return PreservedAnalyses::none();
  }
};

/**
 * 🎯 Step 5: 代码生成（Codegen）
 * 
 * 思路：
 *   将优化后的 schedule tree 转换回 LLVM IR。
 *   使用 isl 的 AST 生成器。
 */
struct CodeGenPass : public PassInfoMixin<CodeGenPass> {
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &FAM) {
    auto *S = getScopFromMetadata(F);
    if (!S) return PreservedAnalyses::all();

    isl_ctx *Ctx = S->getIslCtx();

    // 1. 获取最终调度
    isl_schedule *FinalSchedule = S->getSchedule();

    // 2. 创建 AST 生成器
    isl_ast_build *Build = isl_ast_build_alloc(Ctx);
    
    // 设置选项：启用 tiling
    isl_ast_build_set_option(Build, 
        isl_ast_build_set_at_each_domain(Build, 
            "{domain[i,j] -> tile[floor(i/32), floor(j/32)]]}"));

    // 3. 生成 AST
    isl_ast_node *AST = isl_ast_build_node_from(schedule(Build, FinalSchedule);

    // 4. 遍历 AST，生成 LLVM IR
    generateLLVMFromAST(AST, F);

    // 👉 最终生成优化后的循环嵌套

    return PreservedAnalyses::none();
  }
};

/**
 * 🎯 注册所有 Pass
 */
void registerPollyPasses(PassBuilder &PB) {
  PB.registerAnalysisRegistrationCallback(
      [](FunctionAnalysisManager &FAM) {
        FAM.registerPass([&] { return ScopDetectionPass(); });
      });

  PB.registerPipelineParsingCallback(
      [&](StringRef Name, FunctionPassManager &FPM, bool) {
        if (Name == "polly-scop") {
          FPM.addPass(BuildScopPass());
          FPM.addPass(DependenceAnalysisPass());
          FPM.addPass(OptimizeSchedulePass());
          FPM.addPass(CodeGenPass());
          return true;
        }
        return false;
      });
}
