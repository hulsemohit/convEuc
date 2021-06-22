theory Prop05
	imports Axioms Definitions Theorems
begin

theorem Prop05:
	assumes: `axioms`
		"tri_isos A B C"
	shows: "ang_eq A B C A C B"
proof -
	have "triangle A B C \<and> seg_eq A B A C" sorry
	have "triangle A B C" using `triangle A B C \<and> seg_eq A B A C` by blast
	have "seg_eq A B A C" using `triangle A B C \<and> seg_eq A B A C` by blast
	have "seg_eq A C A B" using congruencesymmetric[OF `axioms` `seg_eq A B A C`] .
	have "\<not> col A B C" sorry
	have "\<not> (col C A B)"
	proof (rule ccontr)
		assume "col C A B"
		have "col A B C" using collinearorder[OF `axioms` `col C A B`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col C A B" by blast
	have "ang_eq C A B B A C" using ABCequalsCBA[OF `axioms` `\<not> col C A B`] .
	have "seg_eq C B B C \<and> ang_eq A C B A B C \<and> ang_eq A B C A C B" using Prop04[OF `axioms` `seg_eq A C A B` `seg_eq A B A C` `ang_eq C A B B A C`] .
	have "ang_eq A B C A C B" using `seg_eq C B B C \<and> ang_eq A C B A B C \<and> ang_eq A B C A C B` by blast
	thus ?thesis by blast
qed

end