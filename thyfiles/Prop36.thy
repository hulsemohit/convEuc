theory Prop36
	imports Axioms Definitions Theorems
begin

theorem Prop36:
	assumes: `axioms`
		"parallelogram A B C D"
		"parallelogram E F G H"
		"col A D E"
		"col A D H"
		"col B C F"
		"col B C G"
		"seg_eq B C F G"
	shows: "qua_eq_area A B C D E F G H"
proof -
	have "parallel A B C D \<and> parallel A D B C" sorry
	have "parallel E F G H \<and> parallel E H F G" sorry
	have "parallel A B C D" using `parallel A B C D \<and> parallel A D B C` by blast
	have "parallel E F G H" using `parallel E F G H \<and> parallel E H F G` by blast
	have "parallel E H F G" using `parallel E F G H \<and> parallel E H F G` by blast
	have "\<not> col E H G" using parallelNC[OF `axioms` `parallel E H F G`] by blast
	have "E \<noteq> H" using NCdistinct[OF `axioms` `\<not> col E H G`] by blast
	have "\<not> col A B C" using parallelNC[OF `axioms` `parallel A B C D`] by blast
	have "B \<noteq> C" using NCdistinct[OF `axioms` `\<not> col A B C`] by blast
	have "seg_eq E H F G" using Prop34[OF `axioms` `parallelogram E F G H`] by blast
	have "seg_eq F G E H" using congruencesymmetric[OF `axioms` `seg_eq E H F G`] .
	have "seg_eq B C E H" using congruencetransitive[OF `axioms` `seg_eq B C F G` `seg_eq F G E H`] .
	have "parallel A D B C" using `parallel A B C D \<and> parallel A D B C` by blast
	have "parallel B C A D" using parallelsymmetric[OF `axioms` `parallel A D B C`] .
	have "parallel B C E H" using collinearparallel2[OF `axioms` `parallel B C A D` `col A D E` `col A D H` `E \<noteq> H`] .
	have "parallel E H B C" using parallelsymmetric[OF `axioms` `parallel B C E H`] .
	have "seg_eq E H B C" using congruencesymmetric[OF `axioms` `seg_eq B C E H`] .
	have "cross E C B H \<or> cross E B H C"
	proof (rule ccontr)
		assume "\<not> (cross E C B H \<or> cross E B H C)"
		have "\<not> (cross E C B H) \<and> \<not> (cross E B H C)" using `\<not> (cross E C B H \<or> cross E B H C)` by blast
		have "\<not> (cross E C B H)" using `\<not> (cross E C B H) \<and> \<not> (cross E B H C)` by blast
		have "\<not> (cross E B H C)" using `\<not> (cross E C B H) \<and> \<not> (cross E B H C)` by blast
		have "cross E C B H" using crisscross[OF `axioms` `parallel E H B C` `\<not> (cross E B H C)`] .
		show "False" using `cross E C B H` `\<not> (cross E C B H) \<and> \<not> (cross E B H C)` by blast
	qed
	hence "cross E C B H \<or> cross E B H C" by blast
	consider "cross E C B H"|"cross E B H C" using `cross E C B H \<or> cross E B H C`  by blast
	hence qua_eq_area A B C D E F G H
	proof (cases)
		case 1
		obtain M where "bet E M C \<and> bet B M H" sorry
		have "bet E M C" using `bet E M C \<and> bet B M H` by blast
		have "bet B M H" using `bet E M C \<and> bet B M H` by blast
		have "bet H M B" using betweennesssymmetryE[OF `axioms` `bet B M H`] .
		have "parallel E B H C \<and> seg_eq E B H C" using Prop33[OF `axioms` `parallel E H B C` `seg_eq E H B C` `bet E M C` `bet H M B`] .
		have "parallel E B H C" using `parallel E B H C \<and> seg_eq E B H C` by blast
		have "parallel E B C H" using parallelflip[OF `axioms` `parallel E B H C`] by blast
		have "parallelogram E B C H" sorry
		have "qua_eq_area A B C D E B C H" using Prop35[OF `axioms` `parallelogram A B C D` `parallelogram E B C H` `col A D E` `col A D H`] .
		have "col B C F" using `col B C F` .
		have "col B C G" using `col B C G` .
		have "B \<noteq> C" using `B \<noteq> C` .
		have "col C F G" using collinear4[OF `axioms` `col B C F` `col B C G` `B \<noteq> C`] .
		have "col G F C" using collinearorder[OF `axioms` `col C F G`] by blast
		have "col C B F" using collinearorder[OF `axioms` `col B C F`] by blast
		have "col C B G" using collinearorder[OF `axioms` `col B C G`] by blast
		have "C \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> C`] .
		have "col B F G" using collinear4[OF `axioms` `col C B F` `col C B G` `C \<noteq> B`] .
		have "col G F B" using collinearorder[OF `axioms` `col B F G`] by blast
		have "parallel E H F G" using `parallel E H F G` .
		have "parallel F G E H" using parallelsymmetric[OF `axioms` `parallel E H F G`] .
		have "parallel G F H E" using parallelflip[OF `axioms` `parallel F G E H`] by blast
		have "parallel E F G H" sorry
		have "parallel G H E F" using parallelsymmetric[OF `axioms` `parallel E F G H`] .
		have "parallel G H E F \<and> parallel G F H E" using `parallel G H E F` `parallel G F H E` by blast
		have "parallelogram G H E F" sorry
		have "parallel E B C H" using `parallel E B C H` .
		have "parallel C H E B" using parallelsymmetric[OF `axioms` `parallel E B C H`] .
		have "parallel E H B C" using `parallel E H B C` .
		have "parallel B C E H" using parallelsymmetric[OF `axioms` `parallel E H B C`] .
		have "parallel C B H E" using parallelflip[OF `axioms` `parallel B C E H`] by blast
		have "parallel C H E B \<and> parallel C B H E" using `parallel C H E B` `parallel C B H E` by blast
		have "parallelogram C H E B" sorry
		have "qua_eq_area G H E F C H E B" using Prop35[OF `axioms` `parallelogram G H E F` `parallelogram C H E B` `col G F C` `col G F B`] .
		have "qua_eq_area G H E F E B C H" using EFpermutationE[OF `axioms` `qua_eq_area G H E F C H E B`] by blast
		have "qua_eq_area E B C H G H E F" using EFsymmetricE[OF `axioms` `qua_eq_area G H E F E B C H`] .
		have "qua_eq_area A B C D G H E F" using EFtransitiveE[OF `axioms` `qua_eq_area A B C D E B C H` `qua_eq_area E B C H G H E F`] .
		have "qua_eq_area A B C D E F G H" using EFpermutationE[OF `axioms` `qua_eq_area A B C D G H E F`] by blast
	next
		case 2
		obtain M where "bet E M B \<and> bet H M C" sorry
		have "bet E M B" using `bet E M B \<and> bet H M C` by blast
		have "bet H M C" using `bet E M B \<and> bet H M C` by blast
		have "parallel H E B C" using parallelflip[OF `axioms` `parallel E H B C`] by blast
		have "seg_eq H E B C" using congruenceflip[OF `axioms` `seg_eq E H B C`] by blast
		have "parallel H B E C \<and> seg_eq H B E C" using Prop33[OF `axioms` `parallel H E B C` `seg_eq H E B C` `bet H M C` `bet E M B`] .
		have "parallel H B E C" using `parallel H B E C \<and> seg_eq H B E C` by blast
		have "parallel H B C E" using parallelflip[OF `axioms` `parallel H B E C`] by blast
		have "parallelogram H B C E" sorry
		have "qua_eq_area A B C D H B C E" using Prop35[OF `axioms` `parallelogram A B C D` `parallelogram H B C E` `col A D H` `col A D E`] .
		have "col B C F" using `col B C F` .
		have "col B C G" using `col B C G` .
		have "B \<noteq> C" using `B \<noteq> C` .
		have "col C G F" using collinear4[OF `axioms` `col B C G` `col B C F` `B \<noteq> C`] .
		have "col F G C" using collinearorder[OF `axioms` `col C G F`] by blast
		have "col C B G" using collinearorder[OF `axioms` `col B C G`] by blast
		have "col C B F" using collinearorder[OF `axioms` `col B C F`] by blast
		have "C \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> C`] .
		have "col B G F" using collinear4[OF `axioms` `col C B G` `col C B F` `C \<noteq> B`] .
		have "col F G B" using collinearorder[OF `axioms` `col B G F`] by blast
		have "parallel H E F G" using parallelflip[OF `axioms` `parallel E H F G`] by blast
		have "parallel F G H E" using parallelsymmetric[OF `axioms` `parallel H E F G`] .
		have "parallel F G E H" using parallelflip[OF `axioms` `parallel F G H E`] by blast
		have "parallel F E H G" using parallelflip[OF `axioms` `parallel E F G H`] by blast
		have "parallel F E H G \<and> parallel F G E H" using `parallel F E H G` `parallel F G E H` by blast
		have "parallelogram F E H G" sorry
		have "parallel H B C E" using `parallel H B C E` .
		have "parallel C E H B" using parallelsymmetric[OF `axioms` `parallel H B C E`] .
		have "parallel C B E H" using parallelflip[OF `axioms` `parallel B C E H`] by blast
		have "parallel C E H B \<and> parallel C B E H" using `parallel C E H B` `parallel C B E H` by blast
		have "parallelogram C E H B" sorry
		have "qua_eq_area F E H G C E H B" using Prop35[OF `axioms` `parallelogram F E H G` `parallelogram C E H B` `col F G C` `col F G B`] .
		have "qua_eq_area F E H G H B C E" using EFpermutationE[OF `axioms` `qua_eq_area F E H G C E H B`] by blast
		have "qua_eq_area H B C E F E H G" using EFsymmetricE[OF `axioms` `qua_eq_area F E H G H B C E`] .
		have "qua_eq_area A B C D F E H G" using EFtransitiveE[OF `axioms` `qua_eq_area A B C D H B C E` `qua_eq_area H B C E F E H G`] .
		have "qua_eq_area A B C D E F G H" using EFpermutationE[OF `axioms` `qua_eq_area A B C D F E H G`] by blast
	next
	thus ?thesis by blast
qed

end