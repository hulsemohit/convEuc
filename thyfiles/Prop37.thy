theory Prop37
	imports Axioms Definitions Theorems
begin

theorem Prop37:
	assumes: `axioms`
		"parallel A D B C"
	shows: "tri_eq_area A B C D B C"
proof -
	have "parallel B C A D" using parallelsymmetric[OF `axioms` `parallel A D B C`] .
	have "parallel C B A D" using parallelflip[OF `axioms` `parallel B C A D`] by blast
	have "A = A" using equalityreflexiveE[OF `axioms`] .
	have "D = D" using equalityreflexiveE[OF `axioms`] .
	have "col A D A" using collinear_b `axioms` `A = A` by blast
	have "col A D D" using collinear_b `axioms` `D = D` by blast
	obtain E where "parallelogram A E B C \<and> col A D E" using triangletoparallelogram[OF `axioms` `parallel C B A D` `col A D A`] by blast
	have "parallelogram A E B C" using `parallelogram A E B C \<and> col A D E` by blast
	have "col A D E" using `parallelogram A E B C \<and> col A D E` by blast
	obtain F where "parallelogram D F B C \<and> col A D F" using triangletoparallelogram[OF `axioms` `parallel C B A D` `col A D D`] by blast
	have "parallelogram D F B C" using `parallelogram D F B C \<and> col A D F` by blast
	have "col A D F" using `parallelogram D F B C \<and> col A D F` by blast
	have "parallelogram E B C A" using PGrotate[OF `axioms` `parallelogram A E B C`] .
	have "parallelogram F B C D" using PGrotate[OF `axioms` `parallelogram D F B C`] .
	have "col D A F" using collinearorder[OF `axioms` `col A D F`] by blast
	have "col D A E" using collinearorder[OF `axioms` `col A D E`] by blast
	have "\<not> col C A D" using parallelNC[OF `axioms` `parallel B C A D`] by blast
	have "A \<noteq> D" using NCdistinct[OF `axioms` `\<not> col C A D`] by blast
	have "D \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> D`] .
	have "col A F E" using collinear4[OF `axioms` `col D A F` `col D A E` `D \<noteq> A`] .
	have "col E A D" using collinearorder[OF `axioms` `col A D E`] by blast
	have "col E A F" using collinearorder[OF `axioms` `col A F E`] by blast
	have "qua_eq_area E B C A F B C D" using Prop35[OF `axioms` `parallelogram E B C A` `parallelogram F B C D` `col E A F` `col E A D`] .
	have "tri_cong B E A A C B" using Prop34[OF `axioms` `parallelogram E B C A`] by blast
	have "tri_cong B F D D C B" using Prop34[OF `axioms` `parallelogram F B C D`] by blast
	obtain M where "bet E M C \<and> bet B M A" using diagonalsmeet[OF `axioms` `parallelogram E B C A`] by blast
	have "bet E M C" using `bet E M C \<and> bet B M A` by blast
	have "bet B M A" using `bet E M C \<and> bet B M A` by blast
	obtain m where "bet F m C \<and> bet B m D" using diagonalsmeet[OF `axioms` `parallelogram F B C D`] by blast
	have "bet F m C" using `bet F m C \<and> bet B m D` by blast
	have "bet B m D" using `bet F m C \<and> bet B m D` by blast
	have "col B M A" using collinear_b `axioms` `bet E M C \<and> bet B M A` by blast
	have "col B m D" using collinear_b `axioms` `bet F m C \<and> bet B m D` by blast
	have "col B A M" using collinearorder[OF `axioms` `col B M A`] by blast
	have "col B D m" using collinearorder[OF `axioms` `col B m D`] by blast
	have "parallel E B C A" using parallelogram_f[OF `axioms` `parallelogram E B C A`] by blast
	have "\<not> col E B A" using parallelNC[OF `axioms` `parallel E B C A`] by blast
	have "\<not> col B A E" using NCorder[OF `axioms` `\<not> col E B A`] by blast
	have "oppo_side E B A C" using oppositeside_b[OF `axioms` `bet E M C` `col B A M` `\<not> col B A E`] .
	have "oppo_side C B A E" using oppositesidesymmetric[OF `axioms` `oppo_side E B A C`] .
	have "parallel D F B C" using parallelogram_f[OF `axioms` `parallelogram D F B C`] by blast
	have "\<not> col D F B" using parallelNC[OF `axioms` `parallel D F B C`] by blast
	have "\<not> col B D F" using NCorder[OF `axioms` `\<not> col D F B`] by blast
	have "oppo_side F B D C" using oppositeside_b[OF `axioms` `bet F m C` `col B D m` `\<not> col B D F`] .
	have "oppo_side C B D F" using oppositesidesymmetric[OF `axioms` `oppo_side F B D C`] .
	have "tri_eq_area B E A A C B" using congruentequalE[OF `axioms` `tri_cong B E A A C B`] .
	have "tri_eq_area B E A C B A" using ETpermutationE[OF `axioms` `tri_eq_area B E A A C B`] by blast
	have "tri_eq_area C B A B E A" using ETsymmetricE[OF `axioms` `tri_eq_area B E A C B A`] .
	have "tri_eq_area C B A B A E" using ETpermutationE[OF `axioms` `tri_eq_area C B A B E A`] by blast
	have "tri_eq_area B F D D C B" using congruentequalE[OF `axioms` `tri_cong B F D D C B`] .
	have "tri_eq_area B F D C B D" using ETpermutationE[OF `axioms` `tri_eq_area B F D D C B`] by blast
	have "tri_eq_area C B D B F D" using ETsymmetricE[OF `axioms` `tri_eq_area B F D C B D`] .
	have "tri_eq_area C B D B D F" using ETpermutationE[OF `axioms` `tri_eq_area C B D B F D`] by blast
	have "qua_eq_area E B C A F B C D" using `qua_eq_area E B C A F B C D` .
	have "qua_eq_area E B C A C B F D" using EFpermutationE[OF `axioms` `qua_eq_area E B C A F B C D`] by blast
	have "qua_eq_area C B F D E B C A" using EFsymmetricE[OF `axioms` `qua_eq_area E B C A C B F D`] .
	have "qua_eq_area C B F D C B E A" using EFpermutationE[OF `axioms` `qua_eq_area C B F D E B C A`] by blast
	have "qua_eq_area C B E A C B F D" using EFsymmetricE[OF `axioms` `qua_eq_area C B F D C B E A`] .
	have "tri_eq_area C B A C B D" using halvesofequalsE[OF `axioms` `tri_eq_area C B A B A E` `oppo_side C B A E` `tri_eq_area C B D B D F` `oppo_side C B D F` `qua_eq_area C B E A C B F D`] .
	have "tri_eq_area C B A D B C" using ETpermutationE[OF `axioms` `tri_eq_area C B A C B D`] by blast
	have "tri_eq_area D B C C B A" using ETsymmetricE[OF `axioms` `tri_eq_area C B A D B C`] .
	have "tri_eq_area D B C A B C" using ETpermutationE[OF `axioms` `tri_eq_area D B C C B A`] by blast
	have "tri_eq_area A B C D B C" using ETsymmetricE[OF `axioms` `tri_eq_area D B C A B C`] .
	thus ?thesis by blast
qed

end