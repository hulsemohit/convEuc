theory n10_12
	imports Axioms Definitions Theorems
begin

theorem n10_12:
	assumes: `axioms`
		"ang_right A B C"
		"ang_right A B H"
		"seg_eq B C B H"
	shows: "seg_eq A C A H"
proof -
	obtain D where "bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C" sorry
	have "bet A B D" using `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by simp
	have "seg_eq A B D B" using `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by simp
	obtain F where "bet A B F \<and> seg_eq A B F B \<and> seg_eq A H F H \<and> B \<noteq> H" sorry
	have "bet A B F" using `bet A B F \<and> seg_eq A B F B \<and> seg_eq A H F H \<and> B \<noteq> H` by simp
	have "seg_eq A B F B" using `bet A B F \<and> seg_eq A B F B \<and> seg_eq A H F H \<and> B \<noteq> H` by simp
	have "seg_eq A H F H" using `bet A B F \<and> seg_eq A B F B \<and> seg_eq A H F H \<and> B \<noteq> H` by simp
	have "seg_eq D B A B" using congruencesymmetric[OF `axioms` `seg_eq A B D B`] .
	have "seg_eq D B F B" using congruencetransitive[OF `axioms` `seg_eq D B A B` `seg_eq A B F B`] .
	have "seg_eq B F B D" using doublereverse[OF `axioms` `seg_eq D B F B`] by blast
	have "F = D" using extensionunique[OF `axioms` `bet A B F` `bet A B D` `seg_eq B F B D`] .
	have "seg_eq A H D H" sorry
