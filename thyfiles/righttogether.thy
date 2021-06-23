theory righttogether
	imports n8_2 Euclid4 Geometry NCorder Prop14 betweennotequal collinearright equalanglesreflexive inequalitysymmetric oppositesidesymmetric ray4
begin

theorem righttogether:
	assumes "axioms"
		"ang_right G A B"
		"ang_right B A C"
		"oppo_side G B A C"
	shows "ang_sum_right G A B B A C \<and> bet G A C"
proof -
	have "ang_right B A G" using n8_2[OF `axioms` `ang_right G A B`] .
	have "A \<noteq> G" using rightangle_f[OF `axioms` `ang_right B A G`] by blast
	have "G \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> G`] .
	obtain D where "bet G A D \<and> seg_eq A D G A" using extensionE[OF `axioms` `G \<noteq> A` `G \<noteq> A`]  by  blast
	have "bet G A D" using `bet G A D \<and> seg_eq A D G A` by blast
	have "B = B" using equalityreflexiveE[OF `axioms`] .
	have "A \<noteq> B" using rightangle_f[OF `axioms` `ang_right G A B`] by blast
	have "ray_on A B B" using ray4 `axioms` `B = B` `A \<noteq> B` by blast
	have "supplement G A B B D" using supplement_b[OF `axioms` `ray_on A B B` `bet G A D`] .
	have "\<not> col B A G" using oppositeside_f[OF `axioms` `oppo_side G B A C`] by blast
	have "\<not> col G A B" using NCorder[OF `axioms` `\<not> col B A G`] by blast
	have "ang_eq G A B G A B" using equalanglesreflexive[OF `axioms` `\<not> col G A B`] .
	have "col G A D" using collinear_b `axioms` `bet G A D \<and> seg_eq A D G A` by blast
	have "A \<noteq> D" using betweennotequal[OF `axioms` `bet G A D`] by blast
	have "D \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> D`] .
	have "ang_right D A B" using collinearright[OF `axioms` `ang_right G A B` `col G A D` `D \<noteq> A`] .
	have "ang_right B A D" using n8_2[OF `axioms` `ang_right D A B`] .
	have "ang_eq B A C B A D" using Euclid4[OF `axioms` `ang_right B A C` `ang_right B A D`] .
	have "ang_sum_right G A B B A C" using tworightangles_b[OF `axioms` `supplement G A B B D` `ang_eq G A B G A B` `ang_eq B A C B A D`] .
	have "oppo_side C B A G" using oppositesidesymmetric[OF `axioms` `oppo_side G B A C`] .
	have "bet G A C" using Prop14[OF `axioms` `ang_sum_right G A B B A C` `ray_on A B B` `oppo_side C B A G`] by blast
	have "ang_sum_right G A B B A C \<and> bet G A C" using `ang_sum_right G A B B A C` `bet G A C` by blast
	thus ?thesis by blast
qed

end