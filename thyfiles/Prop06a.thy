theory Prop06a
	imports ABCequalsCBA Geometry Prop03 Prop04 angledistinct angleorderrespectscongruence2 angletrichotomy betweennotequal collinear4 collinearorder congruenceflip equalangleshelper equalanglesreflexive equalanglessymmetric equalanglestransitive inequalitysymmetric ray4
begin

theorem(in euclidean_geometry) Prop06a:
	assumes 
		"triangle A B C"
		"ang_eq A B C A C B"
	shows "\<not> (seg_lt A C A B)"
proof -
	have "A \<noteq> B" using angledistinct[OF `ang_eq A B C A C B`] by blast
	have "A \<noteq> C" using angledistinct[OF `ang_eq A B C A C B`] by blast
	have "B \<noteq> A" using inequalitysymmetric[OF `A \<noteq> B`] .
	have "C \<noteq> A" using inequalitysymmetric[OF `A \<noteq> C`] .
	have "B \<noteq> C" using angledistinct[OF `ang_eq A B C A C B`] by blast
	have "C \<noteq> B" using inequalitysymmetric[OF `B \<noteq> C`] .
	have "\<not> (seg_lt A C A B)"
	proof (rule ccontr)
		assume "\<not> (\<not> (seg_lt A C A B))"
hence "seg_lt A C A B" by blast
		have "seg_eq B A A B" using equalityreverseE.
		obtain D where "bet B D A \<and> seg_eq B D A C" using Prop03[OF `seg_lt A C A B` `seg_eq B A A B`]  by  blast
		have "bet B D A" using `bet B D A \<and> seg_eq B D A C` by blast
		have "seg_eq B D A C" using `bet B D A \<and> seg_eq B D A C` by blast
		have "seg_eq D B A C" using congruenceflip[OF `seg_eq B D A C`] by blast
		have "ray_on B A D" using ray4 `bet B D A \<and> seg_eq B D A C` `B \<noteq> A` by blast
		have "C = C" using equalityreflexiveE.
		have "ray_on B C C" using ray4 `C = C` `B \<noteq> C` by blast
		have "\<not> col A B C" using triangle_f[OF `triangle A B C`] .
		have "ang_eq A B C A B C" using equalanglesreflexive[OF `\<not> col A B C`] .
		have "ang_eq A B C D B C" using equalangleshelper[OF `ang_eq A B C A B C` `ray_on B A D` `ray_on B C C`] .
		have "ang_eq D B C A B C" using equalanglessymmetric[OF `ang_eq A B C D B C`] .
		have "ang_eq D B C A C B" using equalanglestransitive[OF `ang_eq D B C A B C` `ang_eq A B C A C B`] .
		have "seg_eq B D C A" using congruenceflip[OF `seg_eq B D A C`] by blast
		have "seg_eq B C C B" using equalityreverseE.
		have "seg_eq D C A B \<and> ang_eq B D C C A B \<and> ang_eq B C D C B A" using Prop04[OF `seg_eq B D C A` `seg_eq B C C B` `ang_eq D B C A C B`] .
		have "ang_eq B C D C B A" using `seg_eq D C A B \<and> ang_eq B D C C A B \<and> ang_eq B C D C B A` by blast
		have "\<not> (col C B A)"
		proof (rule ccontr)
			assume "\<not> (\<not> (col C B A))"
hence "col C B A" by blast
			have "col A B C" using collinearorder[OF `col C B A`] by blast
			show "False" using `col A B C` `\<not> col A B C` by blast
		qed
		hence "\<not> col C B A" by blast
		have "ang_eq C B A A B C" using ABCequalsCBA[OF `\<not> col C B A`] .
		have "ang_eq B C D A B C" using equalanglestransitive[OF `ang_eq B C D C B A` `ang_eq C B A A B C`] .
		have "ang_eq A B C A C B" using `ang_eq A B C A C B` .
		have "ang_eq B C D A C B" using equalanglestransitive[OF `ang_eq B C D A B C` `ang_eq A B C A C B`] .
		have "\<not> (col A C B)"
		proof (rule ccontr)
			assume "\<not> (\<not> (col A C B))"
hence "col A C B" by blast
			have "col A B C" using collinearorder[OF `col A C B`] by blast
			show "False" using `col A B C` `\<not> col A B C` by blast
		qed
		hence "\<not> col A C B" by blast
		have "ang_eq A C B B C A" using ABCequalsCBA[OF `\<not> col A C B`] .
		have "ang_eq B C D B C A" using equalanglestransitive[OF `ang_eq B C D A C B` `ang_eq A C B B C A`] .
		have "ang_eq B C A B C D" using equalanglessymmetric[OF `ang_eq B C D B C A`] .
		have "B = B" using equalityreflexiveE.
		have "A = A" using equalityreflexiveE.
		have "ray_on C B B" using ray4 `B = B` `C \<noteq> B` by blast
		have "ray_on C A A" using ray4 `A = A` `C \<noteq> A` by blast
		have "bet B D A" using `bet B D A` .
		have "\<not> (col B C D)"
		proof (rule ccontr)
			assume "\<not> (\<not> (col B C D))"
hence "col B C D" by blast
			have "col B D A" using collinear_b `bet B D A \<and> seg_eq B D A C` by blast
			have "col D B A" using collinearorder[OF `col B D A`] by blast
			have "col D B C" using collinearorder[OF `col B C D`] by blast
			have "B \<noteq> D" using betweennotequal[OF `bet B D A`] by blast
			have "D \<noteq> B" using inequalitysymmetric[OF `B \<noteq> D`] .
			have "col B A C" using collinear4[OF `col D B A` `col D B C` `D \<noteq> B`] .
			have "col A B C" using collinearorder[OF `col B A C`] by blast
			show "False" using `col A B C` `\<not> col A B C` by blast
		qed
		hence "\<not> col B C D" by blast
		have "ang_eq B C D B C D" using equalanglesreflexive[OF `\<not> col B C D`] .
		have "ang_lt B C D B C A" using anglelessthan_b[OF `bet B D A` `ray_on C B B` `ray_on C A A` `ang_eq B C D B C D`] .
		have "ang_lt B C A B C A" using angleorderrespectscongruence2[OF `ang_lt B C D B C A` `ang_eq B C A B C D`] .
		have "\<not> (ang_lt B C A B C A)" using angletrichotomy[OF `ang_lt B C A B C A`] .
		show "False" using `\<not> (ang_lt B C A B C A)` `ang_lt B C A B C A` by blast
	qed
	hence "\<not> (seg_lt A C A B)" by blast
	thus ?thesis by blast
qed

end