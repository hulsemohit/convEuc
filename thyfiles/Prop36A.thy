theory Prop36A
	imports Geometry NCdistinct PGsymmetric Prop33 Prop34 Prop35 collinear4 collinearorder collinearparallel2 congruencesymmetric congruencetransitive inequalitysymmetric nullsegment3 parallelNC parallelflip parallelsymmetric
begin

theorem(in euclidean_geometry) Prop36A:
	assumes 
		"parallelogram A B C D"
		"parallelogram E F G H"
		"col A D E"
		"col A D H"
		"col B C F"
		"col B C G"
		"seg_eq B C F G"
		"bet B M H"
		"bet C M E"
	shows "qua_eq_area A B C D E F G H"
proof -
	have "parallel A B C D \<and> parallel A D B C" using parallelogram_f[OF `parallelogram A B C D`] .
	have "parallel A B C D" using `parallel A B C D \<and> parallel A D B C` by blast
	have "seg_eq E H F G" using Prop34[OF `parallelogram E F G H`] by blast
	have "seg_eq F G E H" using congruencesymmetric[OF `seg_eq E H F G`] .
	have "seg_eq B C E H" using congruencetransitive[OF `seg_eq B C F G` `seg_eq F G E H`] .
	have "parallel A D B C" using `parallel A B C D \<and> parallel A D B C` by blast
	have "parallel B C A D" using parallelsymmetric[OF `parallel A D B C`] .
	have "col A D E" using `col A D E` .
	have "col A D H" using `col A D H` .
	have "\<not> col A B C" using parallelNC[OF `parallel A B C D`] by blast
	have "B \<noteq> C" using NCdistinct[OF `\<not> col A B C`] by blast
	have "E \<noteq> H" using nullsegment3[OF `B \<noteq> C` `seg_eq B C E H`] .
	have "parallel B C E H" using collinearparallel2[OF `parallel B C A D` `col A D E` `col A D H` `E \<noteq> H`] .
	have "bet B M H" using `bet B M H` .
	have "bet C M E" using `bet C M E` .
	have "parallel B E C H \<and> seg_eq B E C H" using Prop33[OF `parallel B C E H` `seg_eq B C E H` `bet B M H` `bet C M E`] .
	have "parallel B E C H" using `parallel B E C H \<and> seg_eq B E C H` by blast
	have "parallel E B C H" using parallelflip[OF `parallel B E C H`] by blast
	have "parallel E H B C" using parallelsymmetric[OF `parallel B C E H`] .
	have "parallelogram E B C H" using parallelogram_b[OF `parallel E B C H` `parallel E H B C`] .
	have "qua_eq_area A B C D E B C H" using Prop35[OF `parallelogram A B C D` `parallelogram E B C H` `col A D E` `col A D H`] .
	have "parallelogram C H E B" using PGsymmetric[OF `parallelogram E B C H`] .
	have "\<not> col A B C" using parallelNC[OF `parallel A B C D`] by blast
	have "B \<noteq> C" using NCdistinct[OF `\<not> col A B C`] by blast
	have "C \<noteq> B" using inequalitysymmetric[OF `B \<noteq> C`] .
	have "col B C F" using `col B C F` .
	have "col B C G" using `col B C G` .
	have "col C F G" using collinear4[OF `col B C F` `col B C G` `B \<noteq> C`] .
	have "col G F C" using collinearorder[OF `col C F G`] by blast
	have "col C B F" using collinearorder[OF `col B C F`] by blast
	have "col C B G" using collinearorder[OF `col B C G`] by blast
	have "col B F G" using collinear4[OF `col C B F` `col C B G` `C \<noteq> B`] .
	have "col G F B" using collinearorder[OF `col B F G`] by blast
	have "parallelogram G H E F" using PGsymmetric[OF `parallelogram E F G H`] .
	have "qua_eq_area G H E F C H E B" using Prop35[OF `parallelogram G H E F` `parallelogram C H E B` `col G F C` `col G F B`] .
	have "qua_eq_area G H E F E B C H" using EFpermutationE[OF `qua_eq_area G H E F C H E B`] by blast
	have "qua_eq_area E B C H G H E F" using EFsymmetricE[OF `qua_eq_area G H E F E B C H`] .
	have "qua_eq_area A B C D G H E F" using EFtransitiveE[OF `qua_eq_area A B C D E B C H` `qua_eq_area E B C H G H E F`] .
	have "qua_eq_area A B C D E F G H" using EFpermutationE[OF `qua_eq_area A B C D G H E F`] by blast
	thus ?thesis by blast
qed

end