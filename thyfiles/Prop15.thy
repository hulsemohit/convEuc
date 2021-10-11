theory Prop15
	imports ABCequalsCBA Geometry betweennotequal collinear4 collinearorder equalanglessymmetric equalanglestransitive inequalitysymmetric ray4 supplements
begin

theorem(in euclidean_geometry) Prop15:
	assumes 
		"bet A E B"
		"bet C E D"
		"\<not> col A E C"
	shows "ang_eq A E C D E B \<and> ang_eq C E B A E D"
proof -
	have "E \<noteq> D" using betweennotequal[OF `bet C E D`] by blast
	have "D \<noteq> E" using inequalitysymmetric[OF `E \<noteq> D`] .
	have "E \<noteq> B" using betweennotequal[OF `bet A E B`] by blast
	have "B \<noteq> E" using inequalitysymmetric[OF `E \<noteq> B`] .
	have "\<not> (col B E D)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col B E D))"
hence "col B E D" by blast
		have "col A E B" using collinear_b `bet A E B` by blast
		have "col B E A" using collinearorder[OF `col A E B`] by blast
		have "col E A D" using collinear4[OF `col B E A` `col B E D` `B \<noteq> E`] .
		have "col C E D" using collinear_b `bet C E D` by blast
		have "col D E C" using collinearorder[OF `col C E D`] by blast
		have "col D E A" using collinearorder[OF `col E A D`] by blast
		have "col E C A" using collinear4[OF `col D E C` `col D E A` `D \<noteq> E`] .
		have "col A E C" using collinearorder[OF `col E C A`] by blast
		show "False" using `col A E C` `\<not> col A E C` by blast
	qed
	hence "\<not> col B E D" by blast
	have "D = D" using equalityreflexiveE.
	have "B = B" using equalityreflexiveE.
	have "C = C" using equalityreflexiveE.
	have "ray_on E D D" using ray4 `D = D` `E \<noteq> D` by blast
	have "ray_on E B B" using ray4 `B = B` `E \<noteq> B` by blast
	have "bet B E A" using betweennesssymmetryE[OF `bet A E B`] .
	have "supplement B E D D A" using supplement_b[OF `ray_on E D D` `bet B E A`] .
	have "bet D E C" using betweennesssymmetryE[OF `bet C E D`] .
	have "supplement D E B B C" using supplement_b[OF `ray_on E B B` `bet D E C`] .
	have "\<not> (col A E D)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col A E D))"
hence "col A E D" by blast
		have "col C E D" using collinear_b `bet C E D` by blast
		have "col D E C" using collinearorder[OF `col C E D`] by blast
		have "col D E A" using collinearorder[OF `col A E D`] by blast
		have "D \<noteq> E" using `D \<noteq> E` .
		have "col E C A" using collinear4[OF `col D E C` `col D E A` `D \<noteq> E`] .
		have "col A E C" using collinearorder[OF `col E C A`] by blast
		show "False" using `col A E C` `\<not> col A E C` by blast
	qed
	hence "\<not> col A E D" by blast
	have "ang_eq B E D D E B" using ABCequalsCBA[OF `\<not> col B E D`] .
	have "ang_eq D E A B E C" using supplements[OF `ang_eq B E D D E B` `supplement B E D D A` `supplement D E B B C`] .
	have "\<not> (col B E C)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col B E C))"
hence "col B E C" by blast
		have "col A E B" using collinear_b `bet A E B` by blast
		have "col B E A" using collinearorder[OF `col A E B`] by blast
		have "B \<noteq> E" using `B \<noteq> E` .
		have "col E A C" using collinear4[OF `col B E A` `col B E C` `B \<noteq> E`] .
		have "col A E C" using collinearorder[OF `col E A C`] by blast
		show "False" using `col A E C` `\<not> col A E C` by blast
	qed
	hence "\<not> col B E C" by blast
	have "ang_eq B E C C E B" using ABCequalsCBA[OF `\<not> col B E C`] .
	have "ang_eq D E A C E B" using equalanglestransitive[OF `ang_eq D E A B E C` `ang_eq B E C C E B`] .
	have "ang_eq A E D D E A" using ABCequalsCBA[OF `\<not> col A E D`] .
	have "ang_eq A E D C E B" using equalanglestransitive[OF `ang_eq A E D D E A` `ang_eq D E A C E B`] .
	have "ang_eq C E B A E D" using equalanglessymmetric[OF `ang_eq A E D C E B`] .
	have "\<not> (E = C)"
	proof (rule ccontr)
		assume "\<not> (E \<noteq> C)"
		hence "E = C" by blast
		have "col B E C" using collinear_b `E = C` by blast
		show "False" using `col B E C` `\<not> col B E C` by blast
	qed
	hence "E \<noteq> C" by blast
	have "ray_on E C C" using ray4 `C = C` `E \<noteq> C` by blast
	have "supplement B E C C A" using supplement_b[OF `ray_on E C C` `bet B E A`] .
	have "bet C E D" using betweennesssymmetryE[OF `bet D E C`] .
	have "supplement C E B B D" using supplement_b[OF `ray_on E B B` `bet C E D`] .
	have "\<not> (col A E C)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col A E C))"
hence "col A E C" by blast
		have "col D E C" using collinear_b `bet D E C` by blast
		have "col C E D" using collinearorder[OF `col D E C`] by blast
		have "col C E A" using collinearorder[OF `col A E C`] by blast
		have "C \<noteq> E" using betweennotequal[OF `bet C E D`] by blast
		have "col E D A" using collinear4[OF `col C E D` `col C E A` `C \<noteq> E`] .
		have "col A E D" using collinearorder[OF `col E D A`] by blast
		show "False" using `col A E D` `\<not> col A E D` by blast
	qed
	hence "\<not> col A E C" by blast
	have "ang_eq B E C C E B" using ABCequalsCBA[OF `\<not> col B E C`] .
	have "ang_eq C E A B E D" using supplements[OF `ang_eq B E C C E B` `supplement B E C C A` `supplement C E B B D`] .
	have "\<not> (col B E D)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col B E D))"
hence "col B E D" by blast
		have "col A E B" using collinear_b `bet A E B` by blast
		have "col B E A" using collinearorder[OF `col A E B`] by blast
		have "B \<noteq> E" using `B \<noteq> E` .
		have "col E A D" using collinear4[OF `col B E A` `col B E D` `B \<noteq> E`] .
		have "col A E D" using collinearorder[OF `col E A D`] by blast
		show "False" using `col A E D` `\<not> col A E D` by blast
	qed
	hence "\<not> col B E D" by blast
	have "ang_eq B E D D E B" using ABCequalsCBA[OF `\<not> col B E D`] .
	have "ang_eq C E A D E B" using equalanglestransitive[OF `ang_eq C E A B E D` `ang_eq B E D D E B`] .
	have "ang_eq A E C C E A" using ABCequalsCBA[OF `\<not> col A E C`] .
	have "ang_eq A E C D E B" using equalanglestransitive[OF `ang_eq A E C C E A` `ang_eq C E A D E B`] .
	have "ang_eq A E C D E B \<and> ang_eq C E B A E D" using `ang_eq A E C D E B` `ang_eq C E B A E D` by blast
	thus ?thesis by blast
qed

end