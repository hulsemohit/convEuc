theory n8_2
	imports Axioms Definitions Theorems
begin

theorem n8_2:
	assumes: `axioms`
		"ang_right A B C"
	shows: "ang_right C B A"
proof -
	obtain D where "bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C" sorry
	have "bet A B D" using `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by simp
	have "seg_eq A B D B" using `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by simp
	have "B \<noteq> C" using `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by simp
	have "C \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> C`] .
	obtain E where "bet C B E \<and> seg_eq B E B C" sorry
	have "bet C B E" using `bet C B E \<and> seg_eq B E B C` by simp
	have "seg_eq B E B C" using `bet C B E \<and> seg_eq B E B C` by simp
	have "A \<noteq> B" using betweennotequal[OF `axioms` `bet A B D`] by blast
	have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
	have "C = C" sorry
	have "A = A" sorry
	have "ray_on B C C" sorry
	have "\<not> col A B C" using rightangleNC[OF `axioms` `ang_right A B C`] .
	have "linear_pair A B C C D" sorry
	have "ray_on B A A" sorry
	have "linear_pair C B A A E" sorry
	have "ang_eq A B C C B A" using ABCequalsCBA[OF `axioms` `\<not> col A B C`] .
	have "ang_eq C B D A B E" using supplements[OF `axioms` `ang_eq A B C C B A` `linear_pair A B C C D` `linear_pair C B A A E`] .
	have "seg_eq B C B E" using congruencesymmetric[OF `axioms` `seg_eq B E B C`] .
	have "seg_eq B D B A" using doublereverse[OF `axioms` `seg_eq A B D B`] by blast
