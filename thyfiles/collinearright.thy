theory collinearright
	imports Axioms Definitions Theorems
begin

theorem collinearright:
	assumes: `axioms`
		"ang_right A B D"
		"col A B C"
		"C \<noteq> B"
	shows: "ang_right C B D"
proof -
	have "A = B \<or> A = C \<or> B = C \<or> bet B A C \<or> bet A B C \<or> bet A C B" using col_f[OF `axioms` `col A B C`] .
	have "\<not> col A B D" using rightangleNC[OF `axioms` `ang_right A B D`] .
	have "\<not> (A = B)"
	proof (rule ccontr)
		assume "A = B"
		have "\<not> col A A D" sorry
		have "A = A" using equalityreflexiveE[OF `axioms`] .
		have "col D A A" using col_b `axioms` `A = A` by blast
		have "col A A D" using collinearorder[OF `axioms` `col D A A`] by blast
		show "False" using `col A A D` `\<not> col A A D` by blast
	qed
	hence "A \<noteq> B" by blast
	have "ang_right D B A" using n8_2[OF `axioms` `ang_right A B D`] .
	consider "A = B"|"A = C"|"B = C"|"bet B A C"|"bet A B C"|"bet A C B" using `A = B \<or> A = C \<or> B = C \<or> bet B A C \<or> bet A B C \<or> bet A C B`  by blast
	hence ang_right D B C
	proof (cases)
		case 1
		have "ang_right D B C"
		proof (rule ccontr)
			assume "\<not> (ang_right D B C)"
			have "col A B D" using col_b `axioms` `A = B` by blast
			show "False" using `col A B D` `\<not> col A B D` by blast
		qed
		hence "ang_right D B C" by blast
	next
		case 2
		have "ang_right D B C" sorry
	next
		case 3
		have "ang_right D B C"
		proof (rule ccontr)
			assume "\<not> (ang_right D B C)"
			have "C = B" using equalitysymmetric[OF `axioms` `B = C`] .
			have "C \<noteq> B" using `C \<noteq> B` .
			show "False" using `C \<noteq> B` `C = B` by blast
		qed
		hence "ang_right D B C" by blast
	next
		case 4
		have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
		have "ray_on B A C" using ray4 `axioms` `bet B A C` `B \<noteq> A` by blast
		have "ang_right D B C" using n8_3[OF `axioms` `ang_right D B A` `ray_on B A C`] .
	next
		case 5
		obtain E where "bet A B E \<and> seg_eq A B E B \<and> seg_eq A D E D \<and> B \<noteq> D" sorry
		have "seg_eq A B E B" using `bet A B E \<and> seg_eq A B E B \<and> seg_eq A D E D \<and> B \<noteq> D` by blast
		have "seg_eq A D E D" using `bet A B E \<and> seg_eq A B E B \<and> seg_eq A D E D \<and> B \<noteq> D` by blast
		have "bet A B E" using `bet A B E \<and> seg_eq A B E B \<and> seg_eq A D E D \<and> B \<noteq> D` by blast
		have "B \<noteq> D" using `bet A B E \<and> seg_eq A B E B \<and> seg_eq A D E D \<and> B \<noteq> D` by blast
		have "bet E B A" using betweennesssymmetryE[OF `axioms` `bet A B E`] .
		have "seg_eq E B A B" using congruencesymmetric[OF `axioms` `seg_eq A B E B`] .
		have "seg_eq E D A D" using congruencesymmetric[OF `axioms` `seg_eq A D E D`] .
		have "bet E B A \<and> seg_eq E B A B \<and> seg_eq A D E D \<and> B \<noteq> D" using `bet E B A` `seg_eq E B A B` `bet A B E \<and> seg_eq A B E B \<and> seg_eq A D E D \<and> B \<noteq> D` `bet A B E \<and> seg_eq A B E B \<and> seg_eq A D E D \<and> B \<noteq> D` by blast
		have "ang_right E B D" sorry
		have "ang_right D B E" using n8_2[OF `axioms` `ang_right E B D`] .
		have "bet A B E" using betweennesssymmetryE[OF `axioms` `bet E B A`] .
		have "bet A B C \<and> bet A B E" using `bet A B C` `bet A B E \<and> seg_eq A B E B \<and> seg_eq A D E D \<and> B \<noteq> D` by blast
		have "ray_on B E C" sorry
		have "ang_right D B C" using n8_3[OF `axioms` `ang_right D B E` `ray_on B E C`] .
	next
		case 6
		have "bet B C A" using betweennesssymmetryE[OF `axioms` `bet A C B`] .
		have "C \<noteq> B" using betweennotequal[OF `axioms` `bet A C B`] by blast
		have "B \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> B`] .
		have "ray_on B C A" using ray4 `axioms` `bet B C A` `B \<noteq> C` by blast
		have "ang_right D B A" using n8_2[OF `axioms` `ang_right A B D`] .
		have "ray_on B A C" using ray5[OF `axioms` `ray_on B C A`] .
		have "ang_right D B C" using n8_3[OF `axioms` `ang_right D B A` `ray_on B A C`] .
	next
	have "ang_right C B D" using n8_2[OF `axioms` `ang_right D B C`] .
	thus ?thesis by blast
qed

end