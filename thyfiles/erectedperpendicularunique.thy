theory erectedperpendicularunique
	imports Axioms Definitions Theorems
begin

theorem erectedperpendicularunique:
	assumes: `axioms`
		"ang_right A B C"
		"ang_right A B E"
		"same_side C E A B"
	shows: "ray_on B C E"
proof -
	obtain D where "bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C" using rightangle_f[OF `axioms` `ang_right A B C`] by blast
	have "B \<noteq> C" using `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by blast
	have "B \<noteq> E" using rightangle_f[OF `axioms` `ang_right A B E`] by blast
	obtain H where "ray_on B E H \<and> seg_eq B H B C" using layoff[OF `axioms` `B \<noteq> E` `B \<noteq> C`] by blast
	have "ray_on B E H" using `ray_on B E H \<and> seg_eq B H B C` by blast
	have "seg_eq B H B C" using `ray_on B E H \<and> seg_eq B H B C` by blast
	have "B = B" using equalityreflexiveE[OF `axioms`] .
	have "col A B B" using collinear_b `axioms` `B = B` by blast
	have "same_side C H A B" using sameside2[OF `axioms` `same_side C E A B` `col A B B` `ray_on B E H`] .
	have "ang_right A B H" using n8_3[OF `axioms` `ang_right A B E` `ray_on B E H`] .
	have "seg_eq B C B H" using congruencesymmetric[OF `axioms` `seg_eq B H B C`] .
	have "seg_eq A C A H" using n10_12[OF `axioms` `ang_right A B C` `ang_right A B H` `seg_eq B C B H`] .
	have "seg_eq C A H A" using congruenceflip[OF `axioms` `seg_eq A C A H`] by blast
	have "seg_eq C B H B" using congruenceflip[OF `axioms` `seg_eq B C B H`] by blast
	have "\<not> (A = B)"
	proof (rule ccontr)
		assume "A = B"
		have "col A B C" using collinear_b `axioms` `A = B` by blast
		have "\<not> col A B C" using rightangleNC[OF `axioms` `ang_right A B C`] .
		show "False" using `\<not> col A B C` `col A B C` by blast
	qed
	hence "A \<noteq> B" by blast
	have "C = H" using Prop07[OF `axioms` `A \<noteq> B` `seg_eq C A H A` `seg_eq C B H B` `same_side C H A B`] .
	have "ray_on B E C" using `ray_on B E H` `C = H` by blast
	have "ray_on B C E" using ray5[OF `axioms` `ray_on B E C`] .
	thus ?thesis by blast
qed

end