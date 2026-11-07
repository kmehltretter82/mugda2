LAKE ?= lake
MUGDA2 := .lake/build/bin/mugda2

.PHONY: all build check-axioms test clean

all: build

build:
	$(LAKE) build

check-axioms: build
	@echo "--- Checking for sorry / partial / unsafe / Classical.choice in Lean sources ---"
	@! grep -En '(^|[^`a-zA-Z0-9_])(sorry|partial[[:space:]]+def|unsafe[[:space:]]+def|Classical\.choice)([^`a-zA-Z0-9_]|$$)' Mugda2.lean Main.lean Mugda2/*.lean
	@echo "--- Verifying kernel axiom footprint via #print axioms ---"
	@printf 'import Mugda2.Giralf\n#print axioms Mugda2.Giralf.TransitionTrace.totalActual_add_phi_eq\n#print axioms Mugda2.Giralf.CreditList.storedCredits_eq_linear_potential\n#print axioms Mugda2.Giralf.erase_behavioral_and_cost_adequate\n#print axioms Mugda2.Giralf.giralf_credit_soundness\n#print axioms Mugda2.Giralf.inferCreditBound_ir_cost_le\n#print axioms Mugda2.Giralf.BatchedQ.dequeue_nonempty_exact_amortized\n#print axioms Mugda2.Giralf.batched_fifoRoundtrip_cost_le\n#print axioms Mugda2.Giralf.singleList_satisfies_expABudget\n#print axioms Mugda2.Giralf.expA_implementation_swap_agreement\n' | $(LAKE) env lean --stdin | tee /tmp/mugda2_axioms.txt
	@! grep -Eq "Classical\.choice|sorryAx|Lean\.ofReduceBool" /tmp/mugda2_axioms.txt
	@echo "Zero sorry, zero partial, zero unsafe, zero Classical.choice verified."

test: check-axioms
	@echo "=== Running Mugda2 Giralf / EXP-A Benchmark Executable ==="
	$(MUGDA2)

clean:
	$(LAKE) clean
