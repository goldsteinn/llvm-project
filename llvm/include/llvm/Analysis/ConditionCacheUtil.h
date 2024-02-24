#ifndef LLVM_ANALYSIS_CONDITIONCACHEUTIL_H
#define LLVM_ANALYSIS_CONDITIONCACHEUTIL_H

#include "llvm/IR/PatternMatch.h"
#include <functional>

namespace llvm {

static void addValueAffectedByCondition(
    Value *V, std::function<void(Value *, int)> InsertAffected, int Idx = -1) {
  using namespace llvm::PatternMatch;
  assert(V != nullptr);
  if (isa<Argument>(V) || isa<GlobalValue>(V)) {
    InsertAffected(V, Idx);
  } else if (auto *I = dyn_cast<Instruction>(V)) {
    InsertAffected(V, Idx);

    // Peek through unary operators to find the source of the condition.
    Value *Op;
    if (match(I, m_PtrToInt(m_Value(Op)))) {
      if (isa<Instruction>(Op) || isa<Argument>(Op))
        InsertAffected(Op, Idx);
    }
  }
}

static void findValuesAffectedByCondition(
    Value *Cond, bool IsAssume,
    std::function<void(Value *, int)> InsertAffected) {
  using namespace llvm::PatternMatch;
  auto AddAffected = [&InsertAffected](Value *V) {
    addValueAffectedByCondition(V, InsertAffected);
  };

  SmallVector<Value *, 8> Worklist;
  SmallPtrSet<Value *, 8> Visited;
  Worklist.push_back(Cond);
  while (!Worklist.empty()) {
    Value *V = Worklist.pop_back_val();
    assert(V != nullptr);
    if (!Visited.insert(V).second)
      continue;
    CmpInst::Predicate Pred;
    Value *A, *B, *X;
    AddAffected(V);
    if (!IsAssume && match(V, m_Not(m_Value(A)))) {
      Worklist.push_back(A);
    } else if (!IsAssume && match(V, m_LogicalOp(m_Value(A), m_Value(B)))) {
      Worklist.push_back(A);
      Worklist.push_back(B);
    } else if (match(V, m_Cmp(Pred, m_Value(A), m_Value(B)))) {
      AddAffected(A);
      AddAffected(B);
      if (match(B, m_Constant())) {
        if (Pred == ICmpInst::ICMP_EQ ||
            (!IsAssume && Pred == ICmpInst::ICMP_NE)) {
          if (match(A, m_BitwiseLogic(m_Value(X), m_ConstantInt())) ||
              match(A, m_Shift(m_Value(X), m_ConstantInt())) ||
              match(A, m_Sub(m_ConstantInt(), m_Value(X))))
            AddAffected(X);
        }
        if (Pred == ICmpInst::ICMP_ULT || Pred == ICmpInst::ICMP_UGT) {
          if (match(A, m_Add(m_Value(X), m_ConstantInt())))
            AddAffected(X);
        }
      }

      if ((Pred == ICmpInst::ICMP_SLT || Pred == ICmpInst::ICMP_SGT) &&
          match(A, m_ElementWiseBitCast(m_Value(X))))
        InsertAffected(X, -1);

      if (CmpInst::isFPPredicate(Pred)) {
        // fcmp fneg(x), y
        // fcmp fabs(x), y
        // fcmp fneg(fabs(x)), y
        if (match(A, m_FNeg(m_Value(X))))
          AddAffected(X);
        if (match(A, m_FAbs(m_Value(X))))
          AddAffected(X);
      }
    } else if (match(Cond, m_Intrinsic<Intrinsic::is_fpclass>(m_Value(X),
                                                              m_Value()))) {
      AddAffected(X);
    }
  }
}

} // namespace llvm

#endif
