theory crossimpliesopposite
	imports Axioms Definitions Theorems
begin

theorem crossimpliesopposite:
	assumes: `axioms`
		"cross A B C D"
		"\<not> col A C D"
	shows: "oppo_side A C D B \<and> oppo_side A D C B \<and> oppo_side B C D A \<and> oppo_side B D C A"
proof -
	obtain M where "bet A M B \<and> bet C M D" sorry
	have "bet A M B" using `bet A M B \<and> bet C M D` by simp
	have "bet C M D" using `bet A M B \<and> bet C M D` by simp
	have "col C M D" sorry
	have "col C D M" using collinearorder[OF `axioms` `col C M D`] by blast
	have "\<not> col C D A" using NCorder[OF `axioms` `\<not> col A C D`] by blast
	have "\<not> col D C A" using NCorder[OF `axioms` `\<not> col A C D`] by blast
	have "oppo_side A C D B" sorry
	have "col D C M" using collinearorder[OF `axioms` `col C D M`] by blast
	have "oppo_side A D C B" sorry
	have "oppo_side B C D A" using oppositesidesymmetric[OF `axioms` `oppo_side A C D B`] .
	have "oppo_side B D C A" using oppositesidesymmetric[OF `axioms` `oppo_side A D C B`] .
	have "oppo_side A C D B \<and> oppo_side A D C B \<and> oppo_side B C D A \<and> oppo_side B D C A"  using `oppo_side A C D B` `oppo_side A D C B` `oppo_side B C D A` `oppo_side B D C A` by simp
	thus ?thesis by blast
qed