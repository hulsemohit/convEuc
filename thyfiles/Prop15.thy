theory Prop15
	imports Axioms Definitions Theorems
begin

theorem Prop15:
	assumes: `axioms`
		"bet A E B"
		"bet C E D"
		"\<not> col A E C"
	shows: "ang_eq A E C D E B \<and> ang_eq C E B A E D"
proof -
	have "E \<noteq> D" using betweennotequal[OF `axioms` `bet C E D`] by blast
	have "D \<noteq> E" using inequalitysymmetric[OF `axioms` `E \<noteq> D`] .
	have "E \<noteq> B" using betweennotequal[OF `axioms` `bet A E B`] by blast
	have "B \<noteq> E" using inequalitysymmetric[OF `axioms` `E \<noteq> B`] .
	have "\<not> (col B E D)"
	proof (rule ccontr)
		assume "col B E D"
		have "col A E B" using col_b `axioms` `bet A E B` by blast
		have "col B E A" using collinearorder[OF `axioms` `col A E B`] by blast
		have "col E A D" using collinear4[OF `axioms` `col B E A` `col B E D` `B \<noteq> E`] .
		have "col C E D" using col_b `axioms` `bet C E D` by blast
		have "col D E C" using collinearorder[OF `axioms` `col C E D`] by blast
		have "col D E A" using collinearorder[OF `axioms` `col E A D`] by blast
		have "col E C A" using collinear4[OF `axioms` `col D E C` `col D E A` `D \<noteq> E`] .
		have "col A E C" using collinearorder[OF `axioms` `col E C A`] by blast
		show "False" using `col A E C` `\<not> col A E C` by blast
	qed
	hence "\<not> col B E D" by blast
	have "D = D" using equalityreflexiveE[OF `axioms`] .
	have "B = B" using equalityreflexiveE[OF `axioms`] .
	have "C = C" using equalityreflexiveE[OF `axioms`] .
	have "ray_on E D D" using ray4 `axioms` `D = D` `E \<noteq> D` by blast
	have "ray_on E B B" using ray4 `axioms` `B = B` `E \<noteq> B` by blast
	have "bet B E A" using betweennesssymmetryE[OF `axioms` `bet A E B`] .
	have "linear_pair B E D D A" sorry
	have "bet D E C" using betweennesssymmetryE[OF `axioms` `bet C E D`] .
	have "linear_pair D E B B C" sorry
	have "\<not> (col A E D)"
	proof (rule ccontr)
		assume "col A E D"
		have "col C E D" using col_b `axioms` `bet C E D` by blast
		have "col D E C" using collinearorder[OF `axioms` `col C E D`] by blast
		have "col D E A" using collinearorder[OF `axioms` `col A E D`] by blast
		have "D \<noteq> E" using `D \<noteq> E` .
		have "col E C A" using collinear4[OF `axioms` `col D E C` `col D E A` `D \<noteq> E`] .
		have "col A E C" using collinearorder[OF `axioms` `col E C A`] by blast
		show "False" using `col A E C` `\<not> col A E C` by blast
	qed
	hence "\<not> col A E D" by blast
	have "ang_eq B E D D E B" using ABCequalsCBA[OF `axioms` `\<not> col B E D`] .
	have "ang_eq D E A B E C" using supplements[OF `axioms` `ang_eq B E D D E B` `linear_pair B E D D A` `linear_pair D E B B C`] .
	have "\<not> (col B E C)"
	proof (rule ccontr)
		assume "col B E C"
		have "col A E B" using col_b `axioms` `bet A E B` by blast
		have "col B E A" using collinearorder[OF `axioms` `col A E B`] by blast
		have "B \<noteq> E" using `B \<noteq> E` .
		have "col E A C" using collinear4[OF `axioms` `col B E A` `col B E C` `B \<noteq> E`] .
		have "col A E C" using collinearorder[OF `axioms` `col E A C`] by blast
		show "False" using `col A E C` `\<not> col A E C` by blast
	qed
	hence "\<not> col B E C" by blast
	have "ang_eq B E C C E B" using ABCequalsCBA[OF `axioms` `\<not> col B E C`] .
	have "ang_eq D E A C E B" using equalanglestransitive[OF `axioms` `ang_eq D E A B E C` `ang_eq B E C C E B`] .
	have "ang_eq A E D D E A" using ABCequalsCBA[OF `axioms` `\<not> col A E D`] .
	have "ang_eq A E D C E B" using equalanglestransitive[OF `axioms` `ang_eq A E D D E A` `ang_eq D E A C E B`] .
	have "ang_eq C E B A E D" using equalanglessymmetric[OF `axioms` `ang_eq A E D C E B`] .
	have "\<not> (E = C)"
	proof (rule ccontr)
		assume "E = C"
		have "col B E C" using col_b `axioms` `E = C` by blast
		show "False" using `col B E C` `\<not> col B E C` by blast
	qed
	hence "E \<noteq> C" by blast
	have "ray_on E C C" using ray4 `axioms` `C = C` `E \<noteq> C` by blast
	have "linear_pair B E C C A" sorry
	have "bet C E D" using betweennesssymmetryE[OF `axioms` `bet D E C`] .
	have "linear_pair C E B B D" sorry
	have "\<not> (col A E C)"
	proof (rule ccontr)
		assume "col A E C"
		have "col D E C" using col_b `axioms` `bet D E C` by blast
		have "col C E D" using collinearorder[OF `axioms` `col D E C`] by blast
		have "col C E A" using collinearorder[OF `axioms` `col A E C`] by blast
		have "C \<noteq> E" using betweennotequal[OF `axioms` `bet C E D`] by blast
		have "col E D A" using collinear4[OF `axioms` `col C E D` `col C E A` `C \<noteq> E`] .
		have "col A E D" using collinearorder[OF `axioms` `col E D A`] by blast
		show "False" using `col A E D` `\<not> col A E D` by blast
	qed
	hence "\<not> col A E C" by blast
	have "ang_eq B E C C E B" using ABCequalsCBA[OF `axioms` `\<not> col B E C`] .
	have "ang_eq C E A B E D" using supplements[OF `axioms` `ang_eq B E C C E B` `linear_pair B E C C A` `linear_pair C E B B D`] .
	have "\<not> (col B E D)"
	proof (rule ccontr)
		assume "col B E D"
		have "col A E B" using col_b `axioms` `bet A E B` by blast
		have "col B E A" using collinearorder[OF `axioms` `col A E B`] by blast
		have "B \<noteq> E" using `B \<noteq> E` .
		have "col E A D" using collinear4[OF `axioms` `col B E A` `col B E D` `B \<noteq> E`] .
		have "col A E D" using collinearorder[OF `axioms` `col E A D`] by blast
		show "False" using `col A E D` `\<not> col A E D` by blast
	qed
	hence "\<not> col B E D" by blast
	have "ang_eq B E D D E B" using ABCequalsCBA[OF `axioms` `\<not> col B E D`] .
	have "ang_eq C E A D E B" using equalanglestransitive[OF `axioms` `ang_eq C E A B E D` `ang_eq B E D D E B`] .
	have "ang_eq A E C C E A" using ABCequalsCBA[OF `axioms` `\<not> col A E C`] .
	have "ang_eq A E C D E B" using equalanglestransitive[OF `axioms` `ang_eq A E C C E A` `ang_eq C E A D E B`] .
	have "ang_eq A E C D E B \<and> ang_eq C E B A E D" using `ang_eq A E C D E B` `ang_eq C E B A E D` by blast
	thus ?thesis by blast
qed

end