theory Prop26A
	imports Axioms Definitions Theorems
begin

theorem Prop26A:
	assumes: `axioms`
		"triangle A B C"
		"triangle D E F"
		"ang_eq A B C D E F"
		"ang_eq B C A E F D"
		"seg_eq B C E F"
	shows: "seg_eq A B D E \<and> seg_eq A C D F \<and> ang_eq B A C E D F"
proof -
	have "\<not> col A B C" using triangle_f[OF `axioms` `triangle A B C`] .
	have "\<not> (A = B)"
	proof (rule ccontr)
		assume "A = B"
		have "col A B C" using collinear_b `axioms` `A = B` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "A \<noteq> B" by blast
	have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
	have "\<not> (B = C)"
	proof (rule ccontr)
		assume "B = C"
		have "col A B C" using collinear_b `axioms` `B = C` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "B \<noteq> C" by blast
	have "C \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> C`] .
	have "\<not> (A = C)"
	proof (rule ccontr)
		assume "A = C"
		have "col A B C" using collinear_b `axioms` `A = C` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "A \<noteq> C" by blast
	have "C \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> C`] .
	have "\<not> (seg_lt D E A B)"
	proof (rule ccontr)
		assume "seg_lt D E A B"
		have "seg_eq A B B A" using equalityreverseE[OF `axioms`] by blast
		have "seg_lt D E B A" using lessthancongruence[OF `axioms` `seg_lt D E A B` `seg_eq A B B A`] .
		obtain G where "bet B G A \<and> seg_eq B G D E" using lessthan_f[OF `axioms` `seg_lt D E B A`] by blast
		have "bet B G A" using `bet B G A \<and> seg_eq B G D E` by blast
		have "B \<noteq> G" using betweennotequal[OF `axioms` `bet B G A`] by blast
		have "seg_eq B G D E" using `bet B G A \<and> seg_eq B G D E` by blast
		have "seg_eq B G E D" using congruenceflip[OF `axioms` `seg_eq B G D E`] by blast
		have "ray_on B A G" using ray4 `axioms` `bet B G A \<and> seg_eq B G D E` `B \<noteq> A` by blast
		have "C = C" using equalityreflexiveE[OF `axioms`] .
		have "ray_on B C C" using ray4 `axioms` `C = C` `B \<noteq> C` by blast
		have "seg_eq G C G C" using congruencereflexiveE[OF `axioms`] by blast
		have "B = B" using equalityreflexiveE[OF `axioms`] .
		have "G = G" using equalityreflexiveE[OF `axioms`] .
		have "ray_on B G G" using ray4 `axioms` `G = G` `B \<noteq> G` by blast
		have "seg_eq B G B G" using congruencereflexiveE[OF `axioms`] by blast
		have "seg_eq B C B C" using congruencereflexiveE[OF `axioms`] by blast
		have "ang_eq A B C G B C" using equalangles_b[OF `axioms` `ray_on B A G` `ray_on B C C` `ray_on B G G` `ray_on B C C` `seg_eq B G B G` `seg_eq B C B C` `seg_eq G C G C` `\<not> col A B C`] .
		have "ang_eq G B C A B C" using equalanglessymmetric[OF `axioms` `ang_eq A B C G B C`] .
		have "ang_eq G B C D E F" using equalanglestransitive[OF `axioms` `ang_eq G B C A B C` `ang_eq A B C D E F`] .
		have "seg_eq G C D F \<and> ang_eq B G C E D F \<and> ang_eq B C G E F D" using Prop04[OF `axioms` `seg_eq B G E D` `seg_eq B C E F` `ang_eq G B C D E F`] .
		have "ang_eq B C G E F D" using `seg_eq G C D F \<and> ang_eq B G C E D F \<and> ang_eq B C G E F D` by blast
		have "ang_eq E F D B C A" using equalanglessymmetric[OF `axioms` `ang_eq B C A E F D`] .
		have "ang_eq B C G B C A" using equalanglestransitive[OF `axioms` `ang_eq B C G E F D` `ang_eq E F D B C A`] .
		have "ang_eq B C A B C G" using equalanglessymmetric[OF `axioms` `ang_eq B C G B C A`] .
		have "ray_on C B B" using ray4 `axioms` `B = B` `C \<noteq> B` by blast
		have "A = A" using equalityreflexiveE[OF `axioms`] .
		have "ray_on C A A" using ray4 `axioms` `A = A` `C \<noteq> A` by blast
		have "ang_lt B C A B C A" using anglelessthan_b[OF `axioms` `bet B G A` `ray_on C B B` `ray_on C A A` `ang_eq B C A B C G`] .
		have "\<not> (ang_lt B C A B C A)" using angletrichotomy[OF `axioms` `ang_lt B C A B C A`] .
		show "False" using `\<not> (ang_lt B C A B C A)` `ang_lt B C A B C A` by blast
	qed
	hence "\<not> (seg_lt D E A B)" by blast
	have "\<not> (seg_lt A B D E)"
	proof (rule ccontr)
		assume "seg_lt A B D E"
		have "seg_eq D E E D" using equalityreverseE[OF `axioms`] by blast
		have "seg_lt A B E D" using lessthancongruence[OF `axioms` `seg_lt A B D E` `seg_eq D E E D`] .
		obtain G where "bet E G D \<and> seg_eq E G A B" using lessthan_f[OF `axioms` `seg_lt A B E D`] by blast
		have "bet E G D" using `bet E G D \<and> seg_eq E G A B` by blast
		have "seg_eq E G A B" using `bet E G D \<and> seg_eq E G A B` by blast
		have "seg_eq E G B A" using congruenceflip[OF `axioms` `seg_eq E G A B`] by blast
		have "E \<noteq> D" using betweennotequal[OF `axioms` `bet E G D`] by blast
		have "ray_on E D G" using ray4 `axioms` `bet E G D \<and> seg_eq E G A B` `E \<noteq> D` by blast
		have "D = D" using equalityreflexiveE[OF `axioms`] .
		have "F = F" using equalityreflexiveE[OF `axioms`] .
		have "\<not> col D E F" using triangle_f[OF `axioms` `triangle D E F`] .
		have "\<not> (E = F)"
		proof (rule ccontr)
			assume "E = F"
			have "col D E F" using collinear_b `axioms` `E = F` by blast
			show "False" using `col D E F` `\<not> col D E F` by blast
		qed
		hence "E \<noteq> F" by blast
		have "ray_on E F F" using ray4 `axioms` `F = F` `E \<noteq> F` by blast
		have "seg_eq G F G F" using congruencereflexiveE[OF `axioms`] by blast
		have "E = E" using equalityreflexiveE[OF `axioms`] .
		have "G = G" using equalityreflexiveE[OF `axioms`] .
		have "E \<noteq> G" using raystrict[OF `axioms` `ray_on E D G`] .
		have "ray_on E G G" using ray4 `axioms` `G = G` `E \<noteq> G` by blast
		have "seg_eq E G E G" using congruencereflexiveE[OF `axioms`] by blast
		have "seg_eq E F E F" using congruencereflexiveE[OF `axioms`] by blast
		have "ang_eq D E F G E F" using equalangles_b[OF `axioms` `ray_on E D G` `ray_on E F F` `ray_on E G G` `ray_on E F F` `seg_eq E G E G` `seg_eq E F E F` `seg_eq G F G F` `\<not> col D E F`] .
		have "ang_eq G E F D E F" using equalanglessymmetric[OF `axioms` `ang_eq D E F G E F`] .
		have "ang_eq D E F A B C" using equalanglessymmetric[OF `axioms` `ang_eq A B C D E F`] .
		have "ang_eq G E F A B C" using equalanglestransitive[OF `axioms` `ang_eq G E F D E F` `ang_eq D E F A B C`] .
		have "seg_eq E F B C" using congruencesymmetric[OF `axioms` `seg_eq B C E F`] .
		have "seg_eq G F A C \<and> ang_eq E G F B A C \<and> ang_eq E F G B C A" using Prop04[OF `axioms` `seg_eq E G B A` `seg_eq E F B C` `ang_eq G E F A B C`] .
		have "ang_eq E F G B C A" using `seg_eq G F A C \<and> ang_eq E G F B A C \<and> ang_eq E F G B C A` by blast
		have "ang_eq E F G E F D" using equalanglestransitive[OF `axioms` `ang_eq E F G B C A` `ang_eq B C A E F D`] .
		have "ang_eq E F D E F G" using equalanglessymmetric[OF `axioms` `ang_eq E F G E F D`] .
		have "\<not> col E F G" using equalanglesNC[OF `axioms` `ang_eq E F D E F G`] .
		have "ang_eq E F G E F G" using equalanglesreflexive[OF `axioms` `\<not> col E F G`] .
		have "E \<noteq> F" using angledistinct[OF `axioms` `ang_eq A B C D E F`] by blast
		have "F \<noteq> E" using inequalitysymmetric[OF `axioms` `E \<noteq> F`] .
		have "ray_on F E E" using ray4 `axioms` `E = E` `F \<noteq> E` by blast
		have "F \<noteq> D" using angledistinct[OF `axioms` `ang_eq B C A E F D`] by blast
		have "ray_on F D D" using ray4 `axioms` `D = D` `F \<noteq> D` by blast
		have "ang_lt E F D E F D" using anglelessthan_b[OF `axioms` `bet E G D` `ray_on F E E` `ray_on F D D` `ang_eq E F D E F G`] .
		have "\<not> (ang_lt E F D E F D)" using angletrichotomy[OF `axioms` `ang_lt E F D E F D`] .
		show "False" using `\<not> (ang_lt E F D E F D)` `ang_lt E F D E F D` by blast
	qed
	hence "\<not> (seg_lt A B D E)" by blast
	have "\<not> (D = E)"
	proof (rule ccontr)
		assume "D = E"
		have "col D E F" using collinear_b `axioms` `D = E` by blast
		have "\<not> col D E F" using triangle_f[OF `axioms` `triangle D E F`] .
		show "False" using `\<not> col D E F` `col D E F` by blast
	qed
	hence "D \<noteq> E" by blast
	have "D \<noteq> E" using `D \<noteq> E` .
	have "seg_eq A B D E" using trichotomy1[OF `axioms` `\<not> (seg_lt A B D E)` `\<not> (seg_lt D E A B)` `A \<noteq> B` `D \<noteq> E`] .
	have "seg_eq B A E D" using congruenceflip[OF `axioms` `seg_eq A B D E`] by blast
	have "seg_eq A C D F \<and> ang_eq B A C E D F \<and> ang_eq B C A E F D" using Prop04[OF `axioms` `seg_eq B A E D` `seg_eq B C E F` `ang_eq A B C D E F`] .
	have "seg_eq A C D F" using `seg_eq A C D F \<and> ang_eq B A C E D F \<and> ang_eq B C A E F D` by blast
	have "ang_eq B A C E D F" using `seg_eq A C D F \<and> ang_eq B A C E D F \<and> ang_eq B C A E F D` by blast
	have "seg_eq A B D E \<and> seg_eq A C D F \<and> ang_eq B A C E D F" using `seg_eq A B D E` `seg_eq A C D F \<and> ang_eq B A C E D F \<and> ang_eq B C A E F D` `seg_eq A C D F \<and> ang_eq B A C E D F \<and> ang_eq B C A E F D` by blast
	thus ?thesis by blast
qed

end