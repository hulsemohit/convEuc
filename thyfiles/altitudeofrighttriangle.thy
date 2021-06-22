theory altitudeofrighttriangle
	imports Axioms Definitions Theorems
begin

theorem altitudeofrighttriangle:
	assumes: `axioms`
		"ang_right B A C"
		"ang_right A M p"
		"col B C p"
		"col B C M"
	shows: "bet B M C"
proof -
	have "\<not> col B A C" using rightangleNC[OF `axioms` `ang_right B A C`] .
	have "C \<noteq> B" using NCdistinct[OF `axioms` `\<not> col B A C`] by blast
	have "\<not> (B = M)"
	proof (rule ccontr)
		assume "B = M"
		have "ang_right A B p" using `ang_right A M p` `B = M` by blast
		have "col p B C" using collinearorder[OF `axioms` `col B C p`] by blast
		have "ang_right p B A" using n8_2[OF `axioms` `ang_right A B p`] .
		have "ang_right C B A" using collinearright[OF `axioms` `ang_right p B A` `col p B C` `C \<noteq> B`] .
		have "\<not> (ang_right C B A)" using n8_7[OF `axioms` `ang_right B A C`] .
		show "False" using `\<not> (ang_right C B A)` `ang_right C B A` by blast
	qed
	hence "B \<noteq> M" by blast
	have "ang_right p M A" using n8_2[OF `axioms` `ang_right A M p`] .
	have "col C B p" using collinearorder[OF `axioms` `col B C p`] by blast
	have "col C B M" using collinearorder[OF `axioms` `col B C M`] by blast
	have "\<not> col B A C" using rightangleNC[OF `axioms` `ang_right B A C`] .
	have "C \<noteq> B" using NCdistinct[OF `axioms` `\<not> col B A C`] by blast
	have "col B p M" using collinear4[OF `axioms` `col C B p` `col C B M` `C \<noteq> B`] .
	have "col p M B" using collinearorder[OF `axioms` `col B p M`] by blast
	have "ang_right B M A" using collinearright[OF `axioms` `ang_right p M A` `col p M B` `B \<noteq> M`] .
	have "col B C p" using collinearorder[OF `axioms` `col C B p`] by blast
	have "col B C M" using collinearorder[OF `axioms` `col C B M`] by blast
	have "B \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> B`] .
	have "col C p M" using collinear4[OF `axioms` `col B C p` `col B C M` `B \<noteq> C`] .
	have "col p M C" using collinearorder[OF `axioms` `col C p M`] by blast
	have "ang_right C A B" using n8_2[OF `axioms` `ang_right B A C`] .
	have "\<not> (C = M)"
	proof (rule ccontr)
		assume "C = M"
		have "ang_right A C p" using `ang_right A M p` `C = M` by blast
		have "col p C B" using collinearorder[OF `axioms` `col B C p`] by blast
		have "ang_right p C A" using n8_2[OF `axioms` `ang_right A C p`] .
		have "ang_right B C A" using collinearright[OF `axioms` `ang_right p C A` `col p C B` `B \<noteq> C`] .
		have "\<not> (ang_right B C A)" using n8_7[OF `axioms` `ang_right C A B`] .
		show "False" using `\<not> (ang_right B C A)` `ang_right B C A` by blast
	qed
	hence "C \<noteq> M" by blast
	have "ang_right C M A" using collinearright[OF `axioms` `ang_right p M A` `col p M C` `C \<noteq> M`] .
	have "ang_right A M B" using n8_2[OF `axioms` `ang_right B M A`] .
	have "ang_right A M C" using n8_2[OF `axioms` `ang_right C M A`] .
	have "seg_lt M B A B" using legsmallerhypotenuse[OF `axioms` `ang_right A M B`] by blast
	have "seg_lt B A B C" using legsmallerhypotenuse[OF `axioms` `ang_right B A C`] by blast
	have "seg_eq B A A B" using equalityreverseE[OF `axioms`] by blast
	have "seg_lt A B B C" using lessthancongruence2[OF `axioms` `seg_lt B A B C` `seg_eq B A A B`] .
	have "seg_lt M B B C" using lessthantransitive[OF `axioms` `seg_lt M B A B` `seg_lt A B B C`] .
	have "seg_eq M B B M" using equalityreverseE[OF `axioms`] by blast
	have "seg_lt B M B C" using lessthancongruence2[OF `axioms` `seg_lt M B B C` `seg_eq M B B M`] .
	have "seg_lt M C A C" using legsmallerhypotenuse[OF `axioms` `ang_right A M C`] by blast
	have "seg_eq M C C M" using equalityreverseE[OF `axioms`] by blast
	have "seg_lt C M A C" using lessthancongruence2[OF `axioms` `seg_lt M C A C` `seg_eq M C C M`] .
	have "seg_lt A C B C" using legsmallerhypotenuse[OF `axioms` `ang_right B A C`] by blast
	have "seg_lt C M B C" using lessthantransitive[OF `axioms` `seg_lt C M A C` `seg_lt A C B C`] .
	have "\<not> (bet M B C)"
	proof (rule ccontr)
		assume "bet M B C"
		have "bet C B M" using betweennesssymmetryE[OF `axioms` `bet M B C`] .
		have "seg_eq C B C B" using congruencereflexiveE[OF `axioms`] by blast
		have "seg_lt C B C M" using lessthan_b[OF `axioms` `bet C B M` `seg_eq C B C B`] .
		have "seg_eq C B B C" using equalityreverseE[OF `axioms`] by blast
		have "seg_lt B C C M" using lessthancongruence2[OF `axioms` `seg_lt C B C M` `seg_eq C B B C`] .
		have "\<not> (seg_lt C M B C)" using trichotomy2[OF `axioms` `seg_lt B C C M`] .
		show "False" using `\<not> (seg_lt C M B C)` `seg_lt C M B C` by blast
	qed
	hence "\<not> (bet M B C)" by blast
	have "col B C M" using `col B C M` .
	have "B = C \<or> B = M \<or> C = M \<or> bet C B M \<or> bet B C M \<or> bet B M C" using collinear_f[OF `axioms` `col B C M`] .
	consider "B = C"|"B = M"|"C = M"|"bet C B M"|"bet B C M"|"bet B M C" using `B = C \<or> B = M \<or> C = M \<or> bet C B M \<or> bet B C M \<or> bet B M C`  by blast
	hence ray_on B C M
	proof (cases)
		case 1
		have "ray_on B C M"
		proof (rule ccontr)
			assume "\<not> (ray_on B C M)"
			have "B \<noteq> C" using `B \<noteq> C` .
			show "False" using `B \<noteq> C` `B = C` by blast
		qed
		hence "ray_on B C M" by blast
	next
		case 2
		have "ray_on B C M"
		proof (rule ccontr)
			assume "\<not> (ray_on B C M)"
			have "B \<noteq> M" using `B \<noteq> M` .
			show "False" using `B \<noteq> M` `B = M` by blast
		qed
		hence "ray_on B C M" by blast
	next
		case 3
		have "ray_on B C M"
		proof (rule ccontr)
			assume "\<not> (ray_on B C M)"
			have "C \<noteq> M" using `C \<noteq> M` .
			show "False" using `C \<noteq> M` `C = M` by blast
		qed
		hence "ray_on B C M" by blast
	next
		case 4
		have "ray_on B C M"
		proof (rule ccontr)
			assume "\<not> (ray_on B C M)"
			have "bet M B C" using betweennesssymmetryE[OF `axioms` `bet C B M`] .
			have "\<not> (bet M B C)" using `\<not> (bet M B C)` .
			show "False" using `\<not> (bet M B C)` `bet M B C` by blast
		qed
		hence "ray_on B C M" by blast
	next
		case 5
		have "ray_on B C M" using ray4 `axioms` `bet B C M` `B \<noteq> C` by blast
	next
		case 6
		have "ray_on B M C" using ray4 `axioms` `bet B M C` `B \<noteq> M` by blast
		have "ray_on B C M" using ray5[OF `axioms` `ray_on B M C`] .
	next
	have "\<not> (bet B C M)"
	proof (rule ccontr)
		assume "bet B C M"
		have "seg_eq B C B C" using congruencereflexiveE[OF `axioms`] by blast
		have "seg_lt B C B M" using lessthan_b[OF `axioms` `bet B C M` `seg_eq B C B C`] .
		have "\<not> (seg_lt B M B C)" using trichotomy2[OF `axioms` `seg_lt B C B M`] .
		show "False" using `\<not> (seg_lt B M B C)` `seg_lt B M B C` by blast
	qed
	hence "\<not> (bet B C M)" by blast
	consider "B = C"|"B = M"|"C = M"|"bet C B M"|"bet B C M"|"bet B M C" using `B = C \<or> B = M \<or> C = M \<or> bet C B M \<or> bet B C M \<or> bet B M C`  by blast
	hence ray_on C B M
	proof (cases)
		case 1
		have "ray_on C B M"
		proof (rule ccontr)
			assume "\<not> (ray_on C B M)"
			have "B \<noteq> C" using `B \<noteq> C` .
			show "False" using `B \<noteq> C` `B = C` by blast
		qed
		hence "ray_on C B M" by blast
	next
		case 2
		have "ray_on C B M"
		proof (rule ccontr)
			assume "\<not> (ray_on C B M)"
			have "B \<noteq> M" using `B \<noteq> M` .
			show "False" using `B \<noteq> M` `B = M` by blast
		qed
		hence "ray_on C B M" by blast
	next
		case 3
		have "ray_on C B M"
		proof (rule ccontr)
			assume "\<not> (ray_on C B M)"
			have "C \<noteq> M" using `C \<noteq> M` .
			show "False" using `C \<noteq> M` `C = M` by blast
		qed
		hence "ray_on C B M" by blast
	next
		case 4
		have "ray_on C B M" using ray4 `axioms` `bet C B M` `C \<noteq> B` by blast
	next
		case 5
		have "ray_on C B M"
		proof (rule ccontr)
			assume "\<not> (ray_on C B M)"
			have "\<not> (bet B C M)" using `\<not> (bet B C M)` .
			show "False" using `\<not> (bet B C M)` `bet B C M` by blast
		qed
		hence "ray_on C B M" by blast
	next
		case 6
		have "bet C M B" using betweennesssymmetryE[OF `axioms` `bet B M C`] .
		have "ray_on C M B" using ray4 `axioms` `bet C M B` `C \<noteq> M` by blast
		have "ray_on C B M" using ray5[OF `axioms` `ray_on C M B`] .
	next
	have "bet B M C" using tworays[OF `axioms` `ray_on B C M` `ray_on C B M`] .
	thus ?thesis by blast
qed

end