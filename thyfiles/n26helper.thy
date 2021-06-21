theory n26helper
	imports Axioms Definitions Theorems
begin

theorem n26helper:
	assumes: `axioms`
		"triangle A B C"
		"ang_eq A B C D E F"
		"ang_eq B C A E F D"
		"seg_eq A B D E"
	shows: "\<not> (seg_lt E F B C)"
proof -
	have "\<not> col A B C" sorry
	have "ang_eq A B C A B C" using equalanglesreflexive[OF `axioms` `\<not> col A B C`] .
	have "A \<noteq> B" using angledistinct[OF `axioms` `ang_eq A B C A B C`] by blast
	have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
	have "B \<noteq> C" using angledistinct[OF `axioms` `ang_eq A B C A B C`] by blast
	have "C \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> C`] .
	have "A \<noteq> C" using angledistinct[OF `axioms` `ang_eq A B C A B C`] by blast
	have "C \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> C`] .
	have "\<not> (seg_lt E F B C)"
	proof (rule ccontr)
		assume "seg_lt E F B C"
		obtain H where "bet B H C \<and> seg_eq B H E F" sorry
		have "bet B H C" using `bet B H C \<and> seg_eq B H E F` by simp
		have "seg_eq B H E F" using `bet B H C \<and> seg_eq B H E F` by simp
		have "ang_eq A B C A B C" using equalanglesreflexive[OF `axioms` `\<not> col A B C`] .
		have "A = A" using equalityreflexiveE[OF `axioms`] .
		have "ray_on B A A" sorry
		have "ray_on B C H" sorry
		have "ang_eq A B C A B H" using equalangleshelper[OF `axioms` `ang_eq A B C A B C` `ray_on B A A` `ray_on B C H`] .
		have "ang_eq A B H A B C" using equalanglessymmetric[OF `axioms` `ang_eq A B C A B H`] .
		have "ang_eq A B H D E F" using equalanglestransitive[OF `axioms` `ang_eq A B H A B C` `ang_eq A B C D E F`] .
		have "seg_eq B A E D" using congruenceflip[OF `axioms` `seg_eq A B D E`] by blast
		have "seg_eq A H D F \<and> ang_eq B A H E D F \<and> ang_eq B H A E F D" using Prop04[OF `axioms` `seg_eq B A E D` `seg_eq B H E F` `ang_eq A B H D E F`] .
		have "ang_eq E F D B C A" using equalanglessymmetric[OF `axioms` `ang_eq B C A E F D`] .
		have "\<not> (col A C H)"
		proof (rule ccontr)
			assume "col A C H"
			have "col H C A" using collinearorder[OF `axioms` `col A C H`] by blast
			have "col B H C" sorry
			have "col H C B" using collinearorder[OF `axioms` `col B H C`] by blast
			have "H \<noteq> C" using betweennotequal[OF `axioms` `bet B H C`] by blast
			have "col C A B" using collinear4[OF `axioms` `col H C A` `col H C B` `H \<noteq> C`] .
			have "col A B C" using collinearorder[OF `axioms` `col C A B`] by blast
			show "False" sorry
		qed
		hence "\<not> col A C H" by blast
		have "triangle A C H" sorry
		have "bet C H B" using betweennesssymmetryE[OF `axioms` `bet B H C`] .
		have "ang_lt H C A A H B" using Prop16[OF `axioms` `triangle A C H` `bet C H B`] by blast
		have "ray_on C B H" sorry
		have "A = A" using equalityreflexiveE[OF `axioms`] .
		have "ray_on C A A" sorry
		have "\<not> (col B C A)"
		proof (rule ccontr)
			assume "col B C A"
			have "col A B C" using collinearorder[OF `axioms` `col B C A`] by blast
			show "False" sorry
		qed
		hence "\<not> col B C A" by blast
		have "ang_eq B C A B C A" using equalanglesreflexive[OF `axioms` `\<not> col B C A`] .
		have "ang_eq B C A H C A" using equalangleshelper[OF `axioms` `ang_eq B C A B C A` `ray_on C B H` `ray_on C A A`] .
		have "ang_lt B C A A H B" using angleorderrespectscongruence2[OF `axioms` `ang_lt H C A A H B` `ang_eq B C A H C A`] .
		have "ang_lt E F D A H B" using angleorderrespectscongruence2[OF `axioms` `ang_lt B C A A H B` `ang_eq E F D B C A`] .
		have "ang_eq B H A E F D" using `seg_eq A H D F \<and> ang_eq B A H E D F \<and> ang_eq B H A E F D` by simp
		have "\<not> (col A H B)"
		proof (rule ccontr)
			assume "col A H B"
			have "col H B A" using collinearorder[OF `axioms` `col A H B`] by blast
			have "col B H C" sorry
			have "col H B C" using collinearorder[OF `axioms` `col B H C`] by blast
			have "B \<noteq> H" using betweennotequal[OF `axioms` `bet B H C`] by blast
			have "H \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> H`] .
			have "col B A C" using collinear4[OF `axioms` `col H B A` `col H B C` `H \<noteq> B`] .
			have "col A B C" using collinearorder[OF `axioms` `col B A C`] by blast
			show "False" sorry
		qed
		hence "\<not> col A H B" by blast
		have "ang_eq A H B B H A" using ABCequalsCBA[OF `axioms` `\<not> col A H B`] .
		have "ang_eq A H B E F D" using equalanglestransitive[OF `axioms` `ang_eq A H B B H A` `ang_eq B H A E F D`] .
		have "ang_lt A H B A H B" using angleorderrespectscongruence2[OF `axioms` `ang_lt E F D A H B` `ang_eq A H B E F D`] .
		have "\<not> (ang_lt A H B A H B)" using angletrichotomy[OF `axioms` `ang_lt A H B A H B`] .
		show "False" sorry
	qed
	hence "\<not> (seg_lt E F B C)" by blast
	thus ?thesis by blast
qed