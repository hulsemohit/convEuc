theory Prop11
	imports Geometry Prop01 betweennotequal collinearorder congruenceflip doublereverse
begin

theorem Prop11:
	assumes "axioms"
		"bet A C B"
	shows "\<exists> F. ang_right A C F"
proof -
	have "A \<noteq> C" using betweennotequal[OF `axioms` `bet A C B`] by blast
	obtain E where "bet A C E \<and> seg_eq C E A C" using extensionE[OF `axioms` `A \<noteq> C` `A \<noteq> C`]  by  blast
	have "bet A C E" using `bet A C E \<and> seg_eq C E A C` by blast
	have "seg_eq C E A C" using `bet A C E \<and> seg_eq C E A C` by blast
	have "A \<noteq> E" using betweennotequal[OF `axioms` `bet A C E`] by blast
	obtain F where "equilateral A E F \<and> triangle A E F" using Prop01[OF `axioms` `A \<noteq> E`]  by  blast
	have "equilateral A E F" using `equilateral A E F \<and> triangle A E F` by blast
	have "triangle A E F" using `equilateral A E F \<and> triangle A E F` by blast
	have "seg_eq E F F A" using equilateral_f[OF `axioms` `equilateral A E F`] by blast
	have "seg_eq A F F E" using doublereverse[OF `axioms` `seg_eq E F F A`] by blast
	have "seg_eq A F E F" using congruenceflip[OF `axioms` `seg_eq A F F E`] by blast
	have "\<not> (C = F)"
	proof (rule ccontr)
		assume "\<not> (C \<noteq> F)"
		hence "C = F" by blast
		have "col A C E" using collinear_b `axioms` `bet A C E \<and> seg_eq C E A C` by blast
		have "col A F E" using `col A C E` `C = F` by blast
		have "col A E F" using collinearorder[OF `axioms` `col A F E`] by blast
		have "\<not> col A E F" using triangle_f[OF `axioms` `triangle A E F`] .
		show "False" using `\<not> col A E F` `col A E F` by blast
	qed
	hence "C \<noteq> F" by blast
	have "bet A C E" using `bet A C E` .
	have "seg_eq C A E C" using doublereverse[OF `axioms` `seg_eq C E A C`] by blast
	have "seg_eq A C E C" using congruenceflip[OF `axioms` `seg_eq C A E C`] by blast
	have "seg_eq A F E F" using `seg_eq A F E F` .
	have "ang_right A C F" using rightangle_b[OF `axioms` `bet A C E` `seg_eq A C E C` `seg_eq A F E F` `C \<noteq> F`] .
	thus ?thesis by blast
qed

end