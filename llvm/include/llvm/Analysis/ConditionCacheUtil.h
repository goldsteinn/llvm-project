#ifndef LLVM_ANALYSIS_CONDITIONCACHEUTIL_H
#define LLVM_ANALYSIS_CONDITIONCACHEUTIL_H

#include <functional>

namespace llvm {

class Value;

void addValueAffectedByCondition(
    Value *V, std::function<void(Value *, int)> InsertAffected, int Idx = -1);

void findValuesAffectedByCondition(
    Value *Cond, std::function<void(Value *, int)> InsertAffected);

} // namespace llvm

#endif
