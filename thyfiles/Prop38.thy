theory Prop38
	imports Geometry NCdistinct NCorder PGrotate Prop34 Prop36 collinear5 collinearorder collinearparallel2 congruenceflip diagonalsmeet nullsegment3 oppositesidesymmetric parallelNC parallelflip parallelsymmetric triangletoparallelogram
begin

theorem(in euclidean_geometry) Prop38:
	assumes 
		"parallel P Q B C"
		"col P Q A"
		"col P Q D"
		"seg_eq B C E F"
		"col B C E"
		"col B C F"
	shows "tri_eq_area A B C D E F"
proof -
	have "parallel B C P Q" using parallelsymmetric[OF `parallel P Q B C`] .
	have "parallel C B P Q" using parallelflip[OF `parallel B C P Q`] by blast
	obtain G where "parallelogram A G B C \<and> col P Q G" using triangletoparallelogram[OF `parallel C B P Q` `col P Q A`]  by  blast
	have "parallelogram A G B C" using `parallelogram A G B C \<and> col P Q G` by blast
	have "col P Q G" using `parallelogram A G B C \<and> col P Q G` by blast
	have "parallelogram G B C A" using PGrotate[OF `parallelogram A G B C`] .
	have "\<not> col P B C" using parallelNC[OF `parallel P Q B C`] by blast
	have "B \<noteq> C" using NCdistinct[OF `\<not> col P B C`] by blast
	have "E \<noteq> F" using nullsegment3[OF `B \<noteq> C` `seg_eq B C E F`] .
	have "parallel P Q E F" using collinearparallel2[OF `parallel P Q B C` `col B C E` `col B C F` `E \<noteq> F`] .
	have "parallel E F P Q" using parallelsymmetric[OF `parallel P Q E F`] .
	obtain H where "parallelogram D H F E \<and> col P Q H" using triangletoparallelogram[OF `parallel E F P Q` `col P Q D`]  by  blast
	have "parallelogram D H F E" using `parallelogram D H F E \<and> col P Q H` by blast
	have "col P Q H" using `parallelogram D H F E \<and> col P Q H` by blast
	have "parallelogram H F E D" using PGrotate[OF `parallelogram D H F E`] .
	have "seg_eq B C F E" using congruenceflip[OF `seg_eq B C E F`] by blast
	have "\<not> col P Q B" using parallelNC[OF `parallel P Q B C`] by blast
	have "P \<noteq> Q" using NCdistinct[OF `\<not> col P Q B`] by blast
	have "col G A H" using collinear5[OF `P \<noteq> Q` `col P Q G` `col P Q A` `col P Q H`] .
	have "col G A D" using collinear5[OF `P \<noteq> Q` `col P Q G` `col P Q A` `col P Q D`] .
	have "col B C F" using `col B C F` .
	have "col B C E" using `col B C E` .
	have "qua_eq_area G B C A H F E D" using Prop36[OF `parallelogram G B C A` `parallelogram H F E D` `col G A H` `col G A D` `col B C F` `col B C E` `seg_eq B C F E`] .
	have "qua_eq_area G B C A E F H D" using EFpermutationE[OF `qua_eq_area G B C A H F E D`] by blast
	have "qua_eq_area E F H D G B C A" using EFsymmetricE[OF `qua_eq_area G B C A E F H D`] .
	have "qua_eq_area E F H D C B G A" using EFpermutationE[OF `qua_eq_area E F H D G B C A`] by blast
	obtain M where "bet D M F \<and> bet H M E" using diagonalsmeet[OF `parallelogram D H F E`]  by  blast
	have "bet D M F" using `bet D M F \<and> bet H M E` by blast
	have "bet H M E" using `bet D M F \<and> bet H M E` by blast
	have "col D M F" using collinear_b `bet D M F \<and> bet H M E` by blast
	have "col F D M" using collinearorder[OF `col D M F`] by blast
	obtain m where "bet A m B \<and> bet G m C" using diagonalsmeet[OF `parallelogram A G B C`]  by  blast
	have "bet A m B" using `bet A m B \<and> bet G m C` by blast
	have "bet G m C" using `bet A m B \<and> bet G m C` by blast
	have "col A m B" using collinear_b `bet A m B \<and> bet G m C` by blast
	have "col B A m" using collinearorder[OF `col A m B`] by blast
	have "parallel A G B C" using parallelogram_f[OF `parallelogram A G B C`] by blast
	have "\<not> col A G B" using parallelNC[OF `parallel A G B C`] by blast
	have "\<not> col B A G" using NCorder[OF `\<not> col A G B`] by blast
	have "parallel D H F E" using parallelogram_f[OF `parallelogram D H F E`] by blast
	have "\<not> col D H F" using parallelNC[OF `parallel D H F E`] by blast
	have "\<not> col F D H" using NCorder[OF `\<not> col D H F`] by blast
	have "oppo_side G B A C" using oppositeside_b[OF `bet G m C` `col B A m` `\<not> col B A G`] .
	have "oppo_side C B A G" using oppositesidesymmetric[OF `oppo_side G B A C`] .
	have "oppo_side H F D E" using oppositeside_b[OF `bet H M E` `col F D M` `\<not> col F D H`] .
	have "oppo_side E F D H" using oppositesidesymmetric[OF `oppo_side H F D E`] .
	have "parallelogram H F E D" using `parallelogram H F E D` .
	have "tri_cong F H D D E F" using Prop34[OF `parallelogram H F E D`] by blast
	have "tri_eq_area F H D D E F" using congruentequalE[OF `tri_cong F H D D E F`] .
	have "tri_eq_area F H D E F D" using ETpermutationE[OF `tri_eq_area F H D D E F`] by blast
	have "tri_eq_area E F D F H D" using ETsymmetricE[OF `tri_eq_area F H D E F D`] .
	have "tri_eq_area E F D F D H" using ETpermutationE[OF `tri_eq_area E F D F H D`] by blast
	have "parallelogram G B C A" using PGrotate[OF `parallelogram A G B C`] .
	have "tri_cong B G A A C B" using Prop34[OF `parallelogram G B C A`] by blast
	have "tri_eq_area B G A A C B" using congruentequalE[OF `tri_cong B G A A C B`] .
	have "tri_eq_area B G A C B A" using ETpermutationE[OF `tri_eq_area B G A A C B`] by blast
	have "tri_eq_area C B A B G A" using ETsymmetricE[OF `tri_eq_area B G A C B A`] .
	have "tri_eq_area C B A B A G" using ETpermutationE[OF `tri_eq_area C B A B G A`] by blast
	have "tri_eq_area E F D C B A" using halvesofequalsE[OF `tri_eq_area E F D F D H` `oppo_side E F D H` `tri_eq_area C B A B A G` `oppo_side C B A G` `qua_eq_area E F H D C B G A`] .
	have "tri_eq_area E F D A B C" using ETpermutationE[OF `tri_eq_area E F D C B A`] by blast
	have "tri_eq_area A B C E F D" using ETsymmetricE[OF `tri_eq_area E F D A B C`] .
	have "tri_eq_area A B C D E F" using ETpermutationE[OF `tri_eq_area A B C E F D`] by blast
	thus ?thesis by blast
qed

end