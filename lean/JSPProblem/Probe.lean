import JSPProblem.Book
namespace JSP90
open Finset Fintype Set
universe u
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

-- Scratch file used only to probe the availability and the argument order of Mathlib lemmas
-- while developing JSPProblem/Book.lean.  It is deliberately trivial and placeholder-free: the
-- harness scans every .lean file under the problem directory for placeholder tokens, so no
-- unfinished proof term may ever live here.  The findings of these probes are recorded in
-- discovery/JSP-000090/policy.json under "ENVIRONMENT".
#check @Finset.card_eq_one
#check @Finset.card_eq_two
#check @Finset.card_image_of_injective
#check @Finset.card_le_card_of_injOn
#check @Finset.mem_filter
#check @Finset.card_biUnion
#check @Nat.mod_add_div
#check @Nat.le_sub_of_add_le
#check @Nat.le_of_dvd
#check @Nat.mul_le_mul
#check @Nat.mul_le_mul_left
#check @Nat.sub_add_cancel
#check @Nat.add_sub_assoc
#check @Finset.card_eq_one
end JSP90
