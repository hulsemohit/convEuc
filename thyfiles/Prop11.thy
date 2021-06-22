theory Prop11
	imports Axioms Definitions Theorems
begin

theorem Prop11:
	assumes: `axioms`
		"bet A C B"
	shows: "\<exists> F. ang_right A C F"
proof -
	have "A \<noteq> C" using betweennotequal[OF `axioms` `bet A C B`] by blast
	obtain E where "bet A C E \<and> seg_eq C E A C" using extensionE[OF `axioms` `A \<noteq> C` `A \<noteq> C`]  by  blast
	have "bet A C E" using `bet A C E \<and> seg_eq C E A C` by blast
	have "seg_eq C E A C" using `bet A C E \<and> seg_eq C E A C` by blast
	have "A \<noteq> E" using betweennotequal[OF `axioms` `bet A C E`] by blast
	obtain F where "equilateral A E F \<and> triangle A E F" using Prop01[OF `axioms` `A \<noteq> E`]  by  blast
	have "equilateral A E F" using `equilateral A E F \<and> triangle A E F` by blast
	have "triangle A E F" using `equilateral A E F \<and> triangle A E F` by blast
	have "seg_eq E F F A" sorry
	have "seg_eq A F F E" using doublereverse[OF `axioms` `seg_eq E F F A`] by blast
	have "seg_eq A F E F" using congruenceflip[OF `axioms` `seg_eq A F F E`] by blast
	have "\<not> (C = F)"
	proof (rule ccontr)
		assume "C = F"
		have "col A C E" using col_b `axioms` `bet A C E \<and> seg_eq C E A C` by blast
		have "col A F E" sorry
		have "col A E F" using collinearorder[OF `axioms` `col A F E`] by blast
		have "\<not> col A E F" sorry
		show "False" using `\<not> col A E F` `col A E F` by blast
	qed
	hence "C \<noteq> F" by blast
	have "bet A C E" using `bet A C E` .
	have "seg_eq C A E C" using doublereverse[OF `axioms` `seg_eq C E A C`] by blast
	have "seg_eq A C E C" using congruenceflip[OF `axioms` `seg_eq C A E C`] by blast
	have "seg_eq A F E F" using `seg_eq A F E F` .
	have "ang_right A C F" sorry
	thus ?thesis by blast
qed

end