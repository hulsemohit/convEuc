theory altitudeofrighttriangle
	imports n8_2 n8_7 Geometry NCdistinct collinear4 collinearorder collinearright inequalitysymmetric legsmallerhypotenuse lessthancongruence2 lessthantransitive ray4 ray5 rightangleNC trichotomy2 tworays
begin

theorem(in euclidean_geometry) altitudeofrighttriangle:
	assumes 
		"ang_right B A C"
		"ang_right A M p"
		"col B C p"
		"col B C M"
	shows "bet B M C"
proof -
	have "\<not> col B A C" using rightangleNC[OF `ang_right B A C`] .
	have "C \<noteq> B" using NCdistinct[OF `\<not> col B A C`] by blast
	have "\<not> (B = M)"
	proof (rule ccontr)
		assume "\<not> (B \<noteq> M)"
		hence "B = M" by blast
		have "ang_right A B p" using `ang_right A M p` `B = M` by blast
		have "col p B C" using collinearorder[OF `col B C p`] by blast
		have "ang_right p B A" using n8_2[OF `ang_right A B p`] .
		have "ang_right C B A" using collinearright[OF `ang_right p B A` `col p B C` `C \<noteq> B`] .
		have "\<not> (ang_right C B A)" using n8_7[OF `ang_right B A C`] .
		show "False" using `\<not> (ang_right C B A)` `ang_right C B A` by blast
	qed
	hence "B \<noteq> M" by blast
	have "ang_right p M A" using n8_2[OF `ang_right A M p`] .
	have "col C B p" using collinearorder[OF `col B C p`] by blast
	have "col C B M" using collinearorder[OF `col B C M`] by blast
	have "\<not> col B A C" using rightangleNC[OF `ang_right B A C`] .
	have "C \<noteq> B" using NCdistinct[OF `\<not> col B A C`] by blast
	have "col B p M" using collinear4[OF `col C B p` `col C B M` `C \<noteq> B`] .
	have "col p M B" using collinearorder[OF `col B p M`] by blast
	have "ang_right B M A" using collinearright[OF `ang_right p M A` `col p M B` `B \<noteq> M`] .
	have "col B C p" using collinearorder[OF `col C B p`] by blast
	have "col B C M" using collinearorder[OF `col C B M`] by blast
	have "B \<noteq> C" using inequalitysymmetric[OF `C \<noteq> B`] .
	have "col C p M" using collinear4[OF `col B C p` `col B C M` `B \<noteq> C`] .
	have "col p M C" using collinearorder[OF `col C p M`] by blast
	have "ang_right C A B" using n8_2[OF `ang_right B A C`] .
	have "\<not> (C = M)"
	proof (rule ccontr)
		assume "\<not> (C \<noteq> M)"
		hence "C = M" by blast
		have "ang_right A C p" using `ang_right A M p` `C = M` by blast
		have "col p C B" using collinearorder[OF `col B C p`] by blast
		have "ang_right p C A" using n8_2[OF `ang_right A C p`] .
		have "ang_right B C A" using collinearright[OF `ang_right p C A` `col p C B` `B \<noteq> C`] .
		have "\<not> (ang_right B C A)" using n8_7[OF `ang_right C A B`] .
		show "False" using `\<not> (ang_right B C A)` `ang_right B C A` by blast
	qed
	hence "C \<noteq> M" by blast
	have "ang_right C M A" using collinearright[OF `ang_right p M A` `col p M C` `C \<noteq> M`] .
	have "ang_right A M B" using n8_2[OF `ang_right B M A`] .
	have "ang_right A M C" using n8_2[OF `ang_right C M A`] .
	have "seg_lt M B A B" using legsmallerhypotenuse[OF `ang_right A M B`] by blast
	have "seg_lt B A B C" using legsmallerhypotenuse[OF `ang_right B A C`] by blast
	have "seg_eq B A A B" using equalityreverseE.
	have "seg_lt A B B C" using lessthancongruence2[OF `seg_lt B A B C` `seg_eq B A A B`] .
	have "seg_lt M B B C" using lessthantransitive[OF `seg_lt M B A B` `seg_lt A B B C`] .
	have "seg_eq M B B M" using equalityreverseE.
	have "seg_lt B M B C" using lessthancongruence2[OF `seg_lt M B B C` `seg_eq M B B M`] .
	have "seg_lt M C A C" using legsmallerhypotenuse[OF `ang_right A M C`] by blast
	have "seg_eq M C C M" using equalityreverseE.
	have "seg_lt C M A C" using lessthancongruence2[OF `seg_lt M C A C` `seg_eq M C C M`] .
	have "seg_lt A C B C" using legsmallerhypotenuse[OF `ang_right B A C`] by blast
	have "seg_lt C M B C" using lessthantransitive[OF `seg_lt C M A C` `seg_lt A C B C`] .
	have "\<not> (bet M B C)"
	proof (rule ccontr)
		assume "\<not> (\<not> (bet M B C))"
hence "bet M B C" by blast
		have "bet C B M" using betweennesssymmetryE[OF `bet M B C`] .
		have "seg_eq C B C B" using congruencereflexiveE.
		have "seg_lt C B C M" using lessthan_b[OF `bet C B M` `seg_eq C B C B`] .
		have "seg_eq C B B C" using equalityreverseE.
		have "seg_lt B C C M" using lessthancongruence2[OF `seg_lt C B C M` `seg_eq C B B C`] .
		have "\<not> (seg_lt C M B C)" using trichotomy2[OF `seg_lt B C C M`] .
		show "False" using `\<not> (seg_lt C M B C)` `seg_lt C M B C` by blast
	qed
	hence "\<not> (bet M B C)" by blast
	have "col B C M" using `col B C M` .
	have "B = C \<or> B = M \<or> C = M \<or> bet C B M \<or> bet B C M \<or> bet B M C" using collinear_f[OF `col B C M`] .
	consider "B = C"|"B = M"|"C = M"|"bet C B M"|"bet B C M"|"bet B M C" using `B = C \<or> B = M \<or> C = M \<or> bet C B M \<or> bet B C M \<or> bet B M C`  by blast
	hence "ray_on B C M"
	proof (cases)
		assume "B = C"
		have "\<not> (\<not> (ray_on B C M))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (ray_on B C M)))"
hence "\<not> (ray_on B C M)" by blast
			have "B \<noteq> C" using `B \<noteq> C` .
			show "False" using `B \<noteq> C` `B = C` by blast
		qed
		hence "ray_on B C M" by blast
		thus ?thesis by blast
	next
		assume "B = M"
		have "\<not> (\<not> (ray_on B C M))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (ray_on B C M)))"
hence "\<not> (ray_on B C M)" by blast
			have "B \<noteq> M" using `B \<noteq> M` .
			show "False" using `B \<noteq> M` `B = M` by blast
		qed
		hence "ray_on B C M" by blast
		thus ?thesis by blast
	next
		assume "C = M"
		have "\<not> (\<not> (ray_on B C M))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (ray_on B C M)))"
hence "\<not> (ray_on B C M)" by blast
			have "C \<noteq> M" using `C \<noteq> M` .
			show "False" using `C \<noteq> M` `C = M` by blast
		qed
		hence "ray_on B C M" by blast
		thus ?thesis by blast
	next
		assume "bet C B M"
		have "\<not> (\<not> (ray_on B C M))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (ray_on B C M)))"
hence "\<not> (ray_on B C M)" by blast
			have "bet M B C" using betweennesssymmetryE[OF `bet C B M`] .
			have "\<not> (bet M B C)" using `\<not> (bet M B C)` .
			show "False" using `\<not> (bet M B C)` `bet M B C` by blast
		qed
		hence "ray_on B C M" by blast
		thus ?thesis by blast
	next
		assume "bet B C M"
		have "ray_on B C M" using ray4 `bet B C M` `B \<noteq> C` by blast
		thus ?thesis by blast
	next
		assume "bet B M C"
		have "ray_on B M C" using ray4 `bet B M C` `B \<noteq> M` by blast
		have "ray_on B C M" using ray5[OF `ray_on B M C`] .
		thus ?thesis by blast
	qed
	have "\<not> (bet B C M)"
	proof (rule ccontr)
		assume "\<not> (\<not> (bet B C M))"
hence "bet B C M" by blast
		have "seg_eq B C B C" using congruencereflexiveE.
		have "seg_lt B C B M" using lessthan_b[OF `bet B C M` `seg_eq B C B C`] .
		have "\<not> (seg_lt B M B C)" using trichotomy2[OF `seg_lt B C B M`] .
		show "False" using `\<not> (seg_lt B M B C)` `seg_lt B M B C` by blast
	qed
	hence "\<not> (bet B C M)" by blast
	consider "B = C"|"B = M"|"C = M"|"bet C B M"|"bet B C M"|"bet B M C" using `B = C \<or> B = M \<or> C = M \<or> bet C B M \<or> bet B C M \<or> bet B M C`  by blast
	hence "ray_on C B M"
	proof (cases)
		assume "B = C"
		have "\<not> (\<not> (ray_on C B M))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (ray_on C B M)))"
hence "\<not> (ray_on C B M)" by blast
			have "B \<noteq> C" using `B \<noteq> C` .
			show "False" using `B \<noteq> C` `B = C` by blast
		qed
		hence "ray_on C B M" by blast
		thus ?thesis by blast
	next
		assume "B = M"
		have "\<not> (\<not> (ray_on C B M))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (ray_on C B M)))"
hence "\<not> (ray_on C B M)" by blast
			have "B \<noteq> M" using `B \<noteq> M` .
			show "False" using `B \<noteq> M` `B = M` by blast
		qed
		hence "ray_on C B M" by blast
		thus ?thesis by blast
	next
		assume "C = M"
		have "\<not> (\<not> (ray_on C B M))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (ray_on C B M)))"
hence "\<not> (ray_on C B M)" by blast
			have "C \<noteq> M" using `C \<noteq> M` .
			show "False" using `C \<noteq> M` `C = M` by blast
		qed
		hence "ray_on C B M" by blast
		thus ?thesis by blast
	next
		assume "bet C B M"
		have "ray_on C B M" using ray4 `bet C B M` `C \<noteq> B` by blast
		thus ?thesis by blast
	next
		assume "bet B C M"
		have "\<not> (\<not> (ray_on C B M))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (ray_on C B M)))"
hence "\<not> (ray_on C B M)" by blast
			have "\<not> (bet B C M)" using `\<not> (bet B C M)` .
			show "False" using `\<not> (bet B C M)` `bet B C M` by blast
		qed
		hence "ray_on C B M" by blast
		thus ?thesis by blast
	next
		assume "bet B M C"
		have "bet C M B" using betweennesssymmetryE[OF `bet B M C`] .
		have "ray_on C M B" using ray4 `bet C M B` `C \<noteq> M` by blast
		have "ray_on C B M" using ray5[OF `ray_on C M B`] .
		thus ?thesis by blast
	qed
	have "bet B M C" using tworays[OF `ray_on B C M` `ray_on C B M`] .
	thus ?thesis by blast
qed

end