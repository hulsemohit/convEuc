theory Prop28A
	imports Axioms Definitions Theorems
begin

theorem Prop28A:
	assumes: `axioms`
		"bet A G B"
		"bet C H D"
		"bet E G H"
		"ang_eq E G B G H D"
		"same_side B D G H"
	shows: "parallel A B C D"
proof -
	have "same_side D B G H" using samesidesymmetric[OF `axioms` `same_side B D G H`] by blast
	have "\<not> col E G B" using equalangles_f[OF `axioms` `ang_eq E G B G H D`] by blast
	have "G = G" using equalityreflexiveE[OF `axioms`] .
	have "col G H G" using collinear_b `axioms` `G = G` by blast
	have "\<not> (col G H A)"
	proof (rule ccontr)
		assume "col G H A"
		have "col H G A" using collinearorder[OF `axioms` `col G H A`] by blast
		have "col E G H" using collinear_b `axioms` `bet E G H` by blast
		have "col H G E" using collinearorder[OF `axioms` `col E G H`] by blast
		have "G \<noteq> H" using betweennotequal[OF `axioms` `bet E G H`] by blast
		have "H \<noteq> G" using inequalitysymmetric[OF `axioms` `G \<noteq> H`] .
		have "col G A E" using collinear4[OF `axioms` `col H G A` `col H G E` `H \<noteq> G`] .
		have "col A G E" using collinearorder[OF `axioms` `col G A E`] by blast
		have "col A G B" using collinear_b `axioms` `bet A G B` by blast
		have "A \<noteq> G" using betweennotequal[OF `axioms` `bet A G B`] by blast
		have "col G E B" using collinear4[OF `axioms` `col A G E` `col A G B` `A \<noteq> G`] .
		have "col E G B" using collinearorder[OF `axioms` `col G E B`] by blast
		show "False" using `col E G B` `\<not> col E G B` by blast
	qed
	hence "\<not> col G H A" by blast
	have "oppo_side A G H B" using oppositeside_b[OF `axioms` `bet A G B` `col G H G` `\<not> col G H A`] .
	have "oppo_side B G H A" using oppositesidesymmetric[OF `axioms` `oppo_side A G H B`] .
	have "bet B G A" using betweennesssymmetryE[OF `axioms` `bet A G B`] .
	have "ang_eq E G B A G H" using Prop15[OF `axioms` `bet E G H` `bet B G A` `\<not> col E G B`] by blast
	have "ang_eq A G H E G B" using equalanglessymmetric[OF `axioms` `ang_eq E G B A G H`] .
	have "ang_eq A G H G H D" using equalanglestransitive[OF `axioms` `ang_eq A G H E G B` `ang_eq E G B G H D`] .
	have "oppo_side D G H A" using planeseparation[OF `axioms` `same_side D B G H` `oppo_side B G H A`] .
	have "oppo_side A G H D" using oppositesidesymmetric[OF `axioms` `oppo_side D G H A`] .
	have "parallel A B C D" using Prop27[OF `axioms` `bet A G B` `bet C H D` `ang_eq A G H G H D` `oppo_side A G H D`] .
	thus ?thesis by blast
qed

end