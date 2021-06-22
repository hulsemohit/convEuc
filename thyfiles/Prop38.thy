theory Prop38
	imports Axioms Definitions Theorems
begin

theorem Prop38:
	assumes: `axioms`
		"parallel P Q B C"
		"col P Q A"
		"col P Q D"
		"seg_eq B C E F"
		"col B C E"
		"col B C F"
	shows: "tri_eq_area A B C D E F"
proof -
	have "parallel B C P Q" using parallelsymmetric[OF `axioms` `parallel P Q B C`] .
	have "parallel C B P Q" using parallelflip[OF `axioms` `parallel B C P Q`] by blast
	obtain G where "parallelogram A G B C \<and> col P Q G" using triangletoparallelogram[OF `axioms` `parallel C B P Q` `col P Q A`]  by  blast
	have "parallelogram A G B C" using `parallelogram A G B C \<and> col P Q G` by blast
	have "col P Q G" using `parallelogram A G B C \<and> col P Q G` by blast
	have "parallelogram G B C A" using PGrotate[OF `axioms` `parallelogram A G B C`] .
	have "\<not> col P B C" using parallelNC[OF `axioms` `parallel P Q B C`] by blast
	have "B \<noteq> C" using NCdistinct[OF `axioms` `\<not> col P B C`] by blast
	have "E \<noteq> F" using nullsegment3[OF `axioms` `B \<noteq> C` `seg_eq B C E F`] .
	have "parallel P Q E F" using collinearparallel2[OF `axioms` `parallel P Q B C` `col B C E` `col B C F` `E \<noteq> F`] .
	have "parallel E F P Q" using parallelsymmetric[OF `axioms` `parallel P Q E F`] .
	obtain H where "parallelogram D H F E \<and> col P Q H" using triangletoparallelogram[OF `axioms` `parallel E F P Q` `col P Q D`]  by  blast
	have "parallelogram D H F E" using `parallelogram D H F E \<and> col P Q H` by blast
	have "col P Q H" using `parallelogram D H F E \<and> col P Q H` by blast
	have "parallelogram H F E D" using PGrotate[OF `axioms` `parallelogram D H F E`] .
	have "seg_eq B C F E" using congruenceflip[OF `axioms` `seg_eq B C E F`] by blast
	have "\<not> col P Q B" using parallelNC[OF `axioms` `parallel P Q B C`] by blast
	have "P \<noteq> Q" using NCdistinct[OF `axioms` `\<not> col P Q B`] by blast
	have "col G A H" using collinear5[OF `axioms` `P \<noteq> Q` `col P Q G` `col P Q A` `col P Q H`] .
	have "col G A D" using collinear5[OF `axioms` `P \<noteq> Q` `col P Q G` `col P Q A` `col P Q D`] .
	have "col B C F" using `col B C F` .
	have "col B C E" using `col B C E` .
	have "qua_eq_area G B C A H F E D" using Prop36[OF `axioms` `parallelogram G B C A` `parallelogram H F E D` `col G A H` `col G A D` `col B C F` `col B C E` `seg_eq B C F E`] .
	have "qua_eq_area G B C A E F H D" using EFpermutationE[OF `axioms` `qua_eq_area G B C A H F E D`] by blast
	have "qua_eq_area E F H D G B C A" using EFsymmetricE[OF `axioms` `qua_eq_area G B C A E F H D`] .
	have "qua_eq_area E F H D C B G A" using EFpermutationE[OF `axioms` `qua_eq_area E F H D G B C A`] by blast
	obtain M where "bet D M F \<and> bet H M E" using diagonalsmeet[OF `axioms` `parallelogram D H F E`]  by  blast
	have "bet D M F" using `bet D M F \<and> bet H M E` by blast
	have "bet H M E" using `bet D M F \<and> bet H M E` by blast
	have "col D M F" using col_b `axioms` `bet D M F \<and> bet H M E` by blast
	have "col F D M" using collinearorder[OF `axioms` `col D M F`] by blast
	obtain m where "bet A m B \<and> bet G m C" using diagonalsmeet[OF `axioms` `parallelogram A G B C`]  by  blast
	have "bet A m B" using `bet A m B \<and> bet G m C` by blast
	have "bet G m C" using `bet A m B \<and> bet G m C` by blast
	have "col A m B" using col_b `axioms` `bet A m B \<and> bet G m C` by blast
	have "col B A m" using collinearorder[OF `axioms` `col A m B`] by blast
	have "parallel A G B C" sorry
	have "\<not> col A G B" using parallelNC[OF `axioms` `parallel A G B C`] by blast
	have "\<not> col B A G" using NCorder[OF `axioms` `\<not> col A G B`] by blast
	have "parallel D H F E" sorry
	have "\<not> col D H F" using parallelNC[OF `axioms` `parallel D H F E`] by blast
	have "\<not> col F D H" using NCorder[OF `axioms` `\<not> col D H F`] by blast
	have "oppo_side G B A C" sorry
	have "oppo_side C B A G" using oppositesidesymmetric[OF `axioms` `oppo_side G B A C`] .
	have "oppo_side H F D E" sorry
	have "oppo_side E F D H" using oppositesidesymmetric[OF `axioms` `oppo_side H F D E`] .
	have "parallelogram H F E D" using `parallelogram H F E D` .
	have "tri_cong F H D D E F" using Prop34[OF `axioms` `parallelogram H F E D`] by blast
	have "tri_eq_area F H D D E F" using congruentequalE[OF `axioms` `tri_cong F H D D E F`] .
	have "tri_eq_area F H D E F D" using ETpermutationE[OF `axioms` `tri_eq_area F H D D E F`] by blast
	have "tri_eq_area E F D F H D" using ETsymmetricE[OF `axioms` `tri_eq_area F H D E F D`] .
	have "tri_eq_area E F D F D H" using ETpermutationE[OF `axioms` `tri_eq_area E F D F H D`] by blast
	have "parallelogram G B C A" using PGrotate[OF `axioms` `parallelogram A G B C`] .
	have "tri_cong B G A A C B" using Prop34[OF `axioms` `parallelogram G B C A`] by blast
	have "tri_eq_area B G A A C B" using congruentequalE[OF `axioms` `tri_cong B G A A C B`] .
	have "tri_eq_area B G A C B A" using ETpermutationE[OF `axioms` `tri_eq_area B G A A C B`] by blast
	have "tri_eq_area C B A B G A" using ETsymmetricE[OF `axioms` `tri_eq_area B G A C B A`] .
	have "tri_eq_area C B A B A G" using ETpermutationE[OF `axioms` `tri_eq_area C B A B G A`] by blast
	have "tri_eq_area E F D C B A" using halvesofequalsE[OF `axioms` `tri_eq_area E F D F D H` `oppo_side E F D H` `tri_eq_area C B A B A G` `oppo_side C B A G` `qua_eq_area E F H D C B G A`] .
	have "tri_eq_area E F D A B C" using ETpermutationE[OF `axioms` `tri_eq_area E F D C B A`] by blast
	have "tri_eq_area A B C E F D" using ETsymmetricE[OF `axioms` `tri_eq_area E F D A B C`] .
	have "tri_eq_area A B C D E F" using ETpermutationE[OF `axioms` `tri_eq_area A B C E F D`] by blast
	thus ?thesis by blast
qed

end