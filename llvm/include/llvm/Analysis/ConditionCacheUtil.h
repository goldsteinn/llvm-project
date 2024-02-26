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
  auto AddAffected = [&InsertAffected](Value *Val) {
    addValueAffectedByCondition(Val, InsertAffected);
  };

  SmallVector<Value *> Worklist;
  SmallPtrSet<Value *, 8> Visited;
  Value *V = Cond;
  auto GetNextVal = [&Worklist, &Visited, &V]() {
    while (!Worklist.empty()) {
      V = Worklist.pop_back_val();
      if (Visited.insert(V).second)
        return true;
    }
    return false;
  };

  while (true) {
    CmpInst::Predicate Pred;
    Value *A, *B;
    if (match(V, m_LogicalOp(m_Value(A), m_Value(B)))) {
      Worklist.push_back(A);
      Worklist.push_back(B);
    } else if (match(V, m_ICmp(Pred, m_Value(A), m_Constant()))) {
      AddAffected(A);

      if (ICmpInst::isEquality(Pred)) {
        Value *X;
        // (X & C) or (X | C) or (X ^ C).
        // (X << C) or (X >>_s C) or (X >>_u C).
        if (match(A, m_BitwiseLogic(m_Value(X), m_ConstantInt())) ||
            match(A, m_Shift(m_Value(X), m_ConstantInt())))
          AddAffected(X);
      } else {
        Value *X;
        // Handle (A + C1) u< C2, which is the canonical form of
        // A > C3 && A < C4.
        if (match(A, m_Add(m_Value(X), m_ConstantInt())))
          AddAffected(X);
        // Handle icmp slt/sgt (bitcast X to int), 0/-1, which is supported by
        // computeKnownFPClass().
        if ((Pred == ICmpInst::ICMP_SLT || Pred == ICmpInst::ICMP_SGT) &&
            match(A, m_ElementWiseBitCast(m_Value(X))))
          InsertAffected(X, -1);
      }
    } else if (match(Cond, m_CombineOr(m_FCmp(Pred, m_Value(A), m_Constant()),
                                       m_Intrinsic<Intrinsic::is_fpclass>(
                                           m_Value(A), m_Constant())))) {
      // Handle patterns that computeKnownFPClass() support.
      AddAffected(A);
    }

    if (!GetNextVal())
      return;
  }
}

} // namespace llvm

#endif
