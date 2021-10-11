theory Prop26A
	imports Geometry Prop04 angledistinct angletrichotomy betweennotequal congruenceflip congruencesymmetric equalanglesNC equalanglesreflexive equalanglessymmetric equalanglestransitive inequalitysymmetric lessthancongruence ray4 raystrict trichotomy1
begin

theorem(in euclidean_geometry) Prop26A:
	assumes 
		"triangle A B C"
		"triangle D E F"
		"ang_eq A B C D E F"
		"ang_eq B C A E F D"
		"seg_eq B C E F"
	shows "seg_eq A B D E \<and> seg_eq A C D F \<and> ang_eq B A C E D F"
proof -
	have "\<not> col A B C" using triangle_f[OF `triangle A B C`] .
	have "\<not> (A = B)"
	proof (rule ccontr)
		assume "\<not> (A \<noteq> B)"
		hence "A = B" by blast
		have "col A B C" using collinear_b `A = B` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "A \<noteq> B" by blast
	have "B \<noteq> A" using inequalitysymmetric[OF `A \<noteq> B`] .
	have "\<not> (B = C)"
	proof (rule ccontr)
		assume "\<not> (B \<noteq> C)"
		hence "B = C" by blast
		have "col A B C" using collinear_b `B = C` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "B \<noteq> C" by blast
	have "C \<noteq> B" using inequalitysymmetric[OF `B \<noteq> C`] .
	have "\<not> (A = C)"
	proof (rule ccontr)
		assume "\<not> (A \<noteq> C)"
		hence "A = C" by blast
		have "col A B C" using collinear_b `A = C` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "A \<noteq> C" by blast
	have "C \<noteq> A" using inequalitysymmetric[OF `A \<noteq> C`] .
	have "\<not> (seg_lt D E A B)"
	proof (rule ccontr)
		assume "\<not> (\<not> (seg_lt D E A B))"
hence "seg_lt D E A B" by blast
		have "seg_eq A B B A" using equalityreverseE.
		have "seg_lt D E B A" using lessthancongruence[OF `seg_lt D E A B` `seg_eq A B B A`] .
		obtain G where "bet B G A \<and> seg_eq B G D E" using lessthan_f[OF `seg_lt D E B A`]  by  blast
		have "bet B G A" using `bet B G A \<and> seg_eq B G D E` by blast
		have "B \<noteq> G" using betweennotequal[OF `bet B G A`] by blast
		have "seg_eq B G D E" using `bet B G A \<and> seg_eq B G D E` by blast
		have "seg_eq B G E D" using congruenceflip[OF `seg_eq B G D E`] by blast
		have "ray_on B A G" using ray4 `bet B G A \<and> seg_eq B G D E` `B \<noteq> A` by blast
		have "C = C" using equalityreflexiveE.
		have "ray_on B C C" using ray4 `C = C` `B \<noteq> C` by blast
		have "seg_eq G C G C" using congruencereflexiveE.
		have "B = B" using equalityreflexiveE.
		have "G = G" using equalityreflexiveE.
		have "ray_on B G G" using ray4 `G = G` `B \<noteq> G` by blast
		have "seg_eq B G B G" using congruencereflexiveE.
		have "seg_eq B C B C" using congruencereflexiveE.
		have "ang_eq A B C G B C" using equalangles_b[OF `ray_on B A G` `ray_on B C C` `ray_on B G G` `ray_on B C C` `seg_eq B G B G` `seg_eq B C B C` `seg_eq G C G C` `\<not> col A B C`] .
		have "ang_eq G B C A B C" using equalanglessymmetric[OF `ang_eq A B C G B C`] .
		have "ang_eq G B C D E F" using equalanglestransitive[OF `ang_eq G B C A B C` `ang_eq A B C D E F`] .
		have "seg_eq G C D F \<and> ang_eq B G C E D F \<and> ang_eq B C G E F D" using Prop04[OF `seg_eq B G E D` `seg_eq B C E F` `ang_eq G B C D E F`] .
		have "ang_eq B C G E F D" using `seg_eq G C D F \<and> ang_eq B G C E D F \<and> ang_eq B C G E F D` by blast
		have "ang_eq E F D B C A" using equalanglessymmetric[OF `ang_eq B C A E F D`] .
		have "ang_eq B C G B C A" using equalanglestransitive[OF `ang_eq B C G E F D` `ang_eq E F D B C A`] .
		have "ang_eq B C A B C G" using equalanglessymmetric[OF `ang_eq B C G B C A`] .
		have "ray_on C B B" using ray4 `B = B` `C \<noteq> B` by blast
		have "A = A" using equalityreflexiveE.
		have "ray_on C A A" using ray4 `A = A` `C \<noteq> A` by blast
		have "ang_lt B C A B C A" using anglelessthan_b[OF `bet B G A` `ray_on C B B` `ray_on C A A` `ang_eq B C A B C G`] .
		have "\<not> (ang_lt B C A B C A)" using angletrichotomy[OF `ang_lt B C A B C A`] .
		show "False" using `\<not> (ang_lt B C A B C A)` `ang_lt B C A B C A` by blast
	qed
	hence "\<not> (seg_lt D E A B)" by blast
	have "\<not> (seg_lt A B D E)"
	proof (rule ccontr)
		assume "\<not> (\<not> (seg_lt A B D E))"
hence "seg_lt A B D E" by blast
		have "seg_eq D E E D" using equalityreverseE.
		have "seg_lt A B E D" using lessthancongruence[OF `seg_lt A B D E` `seg_eq D E E D`] .
		obtain G where "bet E G D \<and> seg_eq E G A B" using lessthan_f[OF `seg_lt A B E D`]  by  blast
		have "bet E G D" using `bet E G D \<and> seg_eq E G A B` by blast
		have "seg_eq E G A B" using `bet E G D \<and> seg_eq E G A B` by blast
		have "seg_eq E G B A" using congruenceflip[OF `seg_eq E G A B`] by blast
		have "E \<noteq> D" using betweennotequal[OF `bet E G D`] by blast
		have "ray_on E D G" using ray4 `bet E G D \<and> seg_eq E G A B` `E \<noteq> D` by blast
		have "D = D" using equalityreflexiveE.
		have "F = F" using equalityreflexiveE.
		have "\<not> col D E F" using triangle_f[OF `triangle D E F`] .
		have "\<not> (E = F)"
		proof (rule ccontr)
			assume "\<not> (E \<noteq> F)"
			hence "E = F" by blast
			have "col D E F" using collinear_b `E = F` by blast
			show "False" using `col D E F` `\<not> col D E F` by blast
		qed
		hence "E \<noteq> F" by blast
		have "ray_on E F F" using ray4 `F = F` `E \<noteq> F` by blast
		have "seg_eq G F G F" using congruencereflexiveE.
		have "E = E" using equalityreflexiveE.
		have "G = G" using equalityreflexiveE.
		have "E \<noteq> G" using raystrict[OF `ray_on E D G`] .
		have "ray_on E G G" using ray4 `G = G` `E \<noteq> G` by blast
		have "seg_eq E G E G" using congruencereflexiveE.
		have "seg_eq E F E F" using congruencereflexiveE.
		have "ang_eq D E F G E F" using equalangles_b[OF `ray_on E D G` `ray_on E F F` `ray_on E G G` `ray_on E F F` `seg_eq E G E G` `seg_eq E F E F` `seg_eq G F G F` `\<not> col D E F`] .
		have "ang_eq G E F D E F" using equalanglessymmetric[OF `ang_eq D E F G E F`] .
		have "ang_eq D E F A B C" using equalanglessymmetric[OF `ang_eq A B C D E F`] .
		have "ang_eq G E F A B C" using equalanglestransitive[OF `ang_eq G E F D E F` `ang_eq D E F A B C`] .
		have "seg_eq E F B C" using congruencesymmetric[OF `seg_eq B C E F`] .
		have "seg_eq G F A C \<and> ang_eq E G F B A C \<and> ang_eq E F G B C A" using Prop04[OF `seg_eq E G B A` `seg_eq E F B C` `ang_eq G E F A B C`] .
		have "ang_eq E F G B C A" using `seg_eq G F A C \<and> ang_eq E G F B A C \<and> ang_eq E F G B C A` by blast
		have "ang_eq E F G E F D" using equalanglestransitive[OF `ang_eq E F G B C A` `ang_eq B C A E F D`] .
		have "ang_eq E F D E F G" using equalanglessymmetric[OF `ang_eq E F G E F D`] .
		have "\<not> col E F G" using equalanglesNC[OF `ang_eq E F D E F G`] .
		have "ang_eq E F G E F G" using equalanglesreflexive[OF `\<not> col E F G`] .
		have "E \<noteq> F" using angledistinct[OF `ang_eq A B C D E F`] by blast
		have "F \<noteq> E" using inequalitysymmetric[OF `E \<noteq> F`] .
		have "ray_on F E E" using ray4 `E = E` `F \<noteq> E` by blast
		have "F \<noteq> D" using angledistinct[OF `ang_eq B C A E F D`] by blast
		have "ray_on F D D" using ray4 `D = D` `F \<noteq> D` by blast
		have "ang_lt E F D E F D" using anglelessthan_b[OF `bet E G D` `ray_on F E E` `ray_on F D D` `ang_eq E F D E F G`] .
		have "\<not> (ang_lt E F D E F D)" using angletrichotomy[OF `ang_lt E F D E F D`] .
		show "False" using `\<not> (ang_lt E F D E F D)` `ang_lt E F D E F D` by blast
	qed
	hence "\<not> (seg_lt A B D E)" by blast
	have "\<not> (D = E)"
	proof (rule ccontr)
		assume "\<not> (D \<noteq> E)"
		hence "D = E" by blast
		have "col D E F" using collinear_b `D = E` by blast
		have "\<not> col D E F" using triangle_f[OF `triangle D E F`] .
		show "False" using `\<not> col D E F` `col D E F` by blast
	qed
	hence "D \<noteq> E" by blast
	have "D \<noteq> E" using `D \<noteq> E` .
	have "seg_eq A B D E" using trichotomy1[OF `\<not> (seg_lt A B D E)` `\<not> (seg_lt D E A B)` `A \<noteq> B` `D \<noteq> E`] .
	have "seg_eq B A E D" using congruenceflip[OF `seg_eq A B D E`] by blast
	have "seg_eq A C D F \<and> ang_eq B A C E D F \<and> ang_eq B C A E F D" using Prop04[OF `seg_eq B A E D` `seg_eq B C E F` `ang_eq A B C D E F`] .
	have "seg_eq A C D F" using `seg_eq A C D F \<and> ang_eq B A C E D F \<and> ang_eq B C A E F D` by blast
	have "ang_eq B A C E D F" using `seg_eq A C D F \<and> ang_eq B A C E D F \<and> ang_eq B C A E F D` by blast
	have "seg_eq A B D E \<and> seg_eq A C D F \<and> ang_eq B A C E D F" using `seg_eq A B D E` `seg_eq A C D F \<and> ang_eq B A C E D F \<and> ang_eq B C A E F D` `seg_eq A C D F \<and> ang_eq B A C E D F \<and> ang_eq B C A E F D` by blast
	thus ?thesis by blast
qed

end