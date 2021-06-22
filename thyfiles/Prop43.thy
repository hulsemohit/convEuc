theory Prop43
	imports Axioms Definitions Theorems
begin

theorem Prop43:
	assumes: `axioms`
		"parallelogram A B C D"
		"bet A H D"
		"bet A E B"
		"bet D F C"
		"bet B G C"
		"bet A K C"
		"parallelogram E A H K"
		"parallelogram G K F C"
	shows: "qua_eq_area K G B E D F K H"
proof -
	have "parallelogram B A D C" using PGflip[OF `axioms` `parallelogram A B C D`] .
	have "tri_cong A B C C D A" using Prop34[OF `axioms` `parallelogram B A D C`] by blast
	have "tri_eq_area A B C C D A" using congruentequalE[OF `axioms` `tri_cong A B C C D A`] .
	have "tri_cong A E K K H A" using Prop34[OF `axioms` `parallelogram E A H K`] by blast
	have "tri_eq_area A E K K H A" using congruentequalE[OF `axioms` `tri_cong A E K K H A`] .
	have "tri_cong K G C C F K" using Prop34[OF `axioms` `parallelogram G K F C`] by blast
	have "tri_eq_area K G C C F K" using congruentequalE[OF `axioms` `tri_cong K G C C F K`] .
	have "tri_eq_area K G C K C F" using ETpermutationE[OF `axioms` `tri_eq_area K G C C F K`] by blast
	have "tri_eq_area K C F K G C" using ETsymmetricE[OF `axioms` `tri_eq_area K G C K C F`] .
	have "tri_eq_area K C F K C G" using ETpermutationE[OF `axioms` `tri_eq_area K C F K G C`] by blast
	have "tri_eq_area K C G K C F" using ETsymmetricE[OF `axioms` `tri_eq_area K C F K C G`] .
	have "tri_eq_area A B C A C D" using ETpermutationE[OF `axioms` `tri_eq_area A B C C D A`] by blast
	have "tri_eq_area A C D A B C" using ETsymmetricE[OF `axioms` `tri_eq_area A B C A C D`] .
	have "tri_eq_area A C D A C B" using ETpermutationE[OF `axioms` `tri_eq_area A C D A B C`] by blast
	have "tri_eq_area A C B A C D" using ETsymmetricE[OF `axioms` `tri_eq_area A C D A C B`] .
	have "qua_eq_area A K G B A K F D" using cutoff1E[OF `axioms` `bet A K C` `bet A K C` `bet B G C` `bet D F C` `tri_eq_area K C G K C F` `tri_eq_area A C B A C D`] .
	have "bet B E A" using betweennesssymmetryE[OF `axioms` `bet A E B`] .
	have "bet D H A" using betweennesssymmetryE[OF `axioms` `bet A H D`] .
	have "tri_eq_area A E K H A K" using ETpermutationE[OF `axioms` `tri_eq_area A E K K H A`] by blast
	have "tri_eq_area H A K A E K" using ETsymmetricE[OF `axioms` `tri_eq_area A E K H A K`] .
	have "tri_eq_area H A K E A K" using ETpermutationE[OF `axioms` `tri_eq_area H A K A E K`] by blast
	have "tri_eq_area E A K H A K" using ETsymmetricE[OF `axioms` `tri_eq_area H A K E A K`] .
	have "qua_eq_area A K G B F D A K" using EFpermutationE[OF `axioms` `qua_eq_area A K G B A K F D`] by blast
	have "qua_eq_area F D A K A K G B" using EFsymmetricE[OF `axioms` `qua_eq_area A K G B F D A K`] .
	have "qua_eq_area F D A K G B A K" using EFpermutationE[OF `axioms` `qua_eq_area F D A K A K G B`] by blast
	have "qua_eq_area G B A K F D A K" using EFsymmetricE[OF `axioms` `qua_eq_area F D A K G B A K`] .
	have "qua_eq_area G B E K F D H K" sorry
	have "qua_eq_area G B E K D F K H" using EFpermutationE[OF `axioms` `qua_eq_area G B E K F D H K`] by blast
	have "qua_eq_area D F K H G B E K" using EFsymmetricE[OF `axioms` `qua_eq_area G B E K D F K H`] .
	have "qua_eq_area D F K H K G B E" using EFpermutationE[OF `axioms` `qua_eq_area D F K H G B E K`] by blast
	have "qua_eq_area K G B E D F K H" using EFsymmetricE[OF `axioms` `qua_eq_area D F K H K G B E`] .
	thus ?thesis by blast
qed

end