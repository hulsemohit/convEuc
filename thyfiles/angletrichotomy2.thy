theory angletrichotomy2
	imports n3_6a n3_6b ABCequalsCBA Geometry Prop23C angleorderrespectscongruence angleorderrespectscongruence2 betweennotequal collinear4 collinear5 collinearorder equalanglesNC equalangleshelper equalanglesreflexive equalanglessymmetric equalanglestransitive equalitysymmetric inequalitysymmetric oppositesidesymmetric outerconnectivity planeseparation ray4 ray5 rayimpliescollinear sameside2 samesidesymmetric
begin

theorem(in euclidean_geometry) angletrichotomy2:
	assumes 
		"\<not> col A B C"
		"\<not> col D E F"
		"\<not> (ang_eq A B C D E F)"
		"\<not> (ang_lt D E F A B C)"
	shows "ang_lt A B C D E F"
proof -
	have "\<not> (B = A)"
	proof (rule ccontr)
		assume "\<not> (B \<noteq> A)"
		hence "B = A" by blast
		have "A = B" using equalitysymmetric[OF `B = A`] .
		have "col A B C" using collinear_b `A = B` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "B \<noteq> A" by blast
	have "\<not> (B = C)"
	proof (rule ccontr)
		assume "\<not> (B \<noteq> C)"
		hence "B = C" by blast
		have "col A B C" using collinear_b `B = C` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "B \<noteq> C" by blast
	have "\<not> (col B A C)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col B A C))"
hence "col B A C" by blast
		have "col A B C" using collinearorder[OF `col B A C`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col B A C" by blast
	obtain G J where "ray_on B A J \<and> ang_eq G B J D E F \<and> same_side G C B A" using Prop23C[OF `B \<noteq> A` `\<not> col D E F` `\<not> col B A C`]  by  blast
	have "ray_on B A J" using `ray_on B A J \<and> ang_eq G B J D E F \<and> same_side G C B A` by blast
	have "ang_eq G B J D E F" using `ray_on B A J \<and> ang_eq G B J D E F \<and> same_side G C B A` by blast
	have "same_side G C B A" using `ray_on B A J \<and> ang_eq G B J D E F \<and> same_side G C B A` by blast
	have "\<not> col B A G" using sameside_f[OF `same_side G C B A`] by blast
	have "\<not> (B = G)"
	proof (rule ccontr)
		assume "\<not> (B \<noteq> G)"
		hence "B = G" by blast
		have "col B A G" using collinear_b `B = G` by blast
		show "False" using `col B A G` `\<not> col B A G` by blast
	qed
	hence "B \<noteq> G" by blast
	have "\<not> (A = G)"
	proof (rule ccontr)
		assume "\<not> (A \<noteq> G)"
		hence "A = G" by blast
		have "col B A G" using collinear_b `A = G` by blast
		show "False" using `col B A G` `\<not> col B A G` by blast
	qed
	hence "A \<noteq> G" by blast
	have "ang_eq D E F G B J" using equalanglessymmetric[OF `ang_eq G B J D E F`] .
	have "ray_on B J A" using ray5[OF `ray_on B A J`] .
	have "G = G" using equalityreflexiveE.
	have "ray_on B G G" using ray4 `G = G` `B \<noteq> G` by blast
	have "ang_eq D E F G B A" using equalangleshelper[OF `ang_eq D E F G B J` `ray_on B G G` `ray_on B J A`] .
	have "\<not> col G B A" using equalanglesNC[OF `ang_eq D E F G B A`] .
	have "\<not> (col A B G)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col A B G))"
hence "col A B G" by blast
		have "col B A G" using collinearorder[OF `col A B G`] by blast
		show "False" using `col B A G` `\<not> col B A G` by blast
	qed
	hence "\<not> col A B G" by blast
	have "ang_eq G B A D E F" using equalanglessymmetric[OF `ang_eq D E F G B A`] .
	have "ang_eq A B G G B A" using ABCequalsCBA[OF `\<not> col A B G`] .
	have "ang_eq A B G D E F" using equalanglestransitive[OF `ang_eq A B G G B A` `ang_eq G B A D E F`] .
	have "\<not> (col A B G)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col A B G))"
hence "col A B G" by blast
		have "col G B A" using collinearorder[OF `col A B G`] by blast
		show "False" using `col G B A` `\<not> col G B A` by blast
	qed
	hence "\<not> col A B G" by blast
	have "\<not> (G = A)"
	proof (rule ccontr)
		assume "\<not> (G \<noteq> A)"
		hence "G = A" by blast
		have "A = G" using equalitysymmetric[OF `G = A`] .
		have "col A B G" using collinear_b `A = G` by blast
		show "False" using `col A B G` `\<not> col A B G` by blast
	qed
	hence "G \<noteq> A" by blast
	obtain P where "bet G A P \<and> seg_eq A P G A" using extensionE[OF `G \<noteq> A` `G \<noteq> A`]  by  blast
	have "bet G A P" using `bet G A P \<and> seg_eq A P G A` by blast
	have "A = A" using equalityreflexiveE.
	have "col B A A" using collinear_b `A = A` by blast
	have "\<not> (col B A G)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col B A G))"
hence "col B A G" by blast
		have "col G B A" using collinearorder[OF `col B A G`] by blast
		show "False" using `col G B A` `\<not> col G B A` by blast
	qed
	hence "\<not> col B A G" by blast
	have "same_side C G B A" using samesidesymmetric[OF `same_side G C B A`] by blast
	have "oppo_side G B A P" using oppositeside_b[OF `bet G A P` `col B A A` `\<not> col B A G`] .
	have "oppo_side C B A P" using planeseparation[OF `same_side C G B A` `oppo_side G B A P`] .
	obtain R where "bet C R P \<and> col B A R \<and> \<not> col B A C" using oppositeside_f[OF `oppo_side C B A P`]  by  blast
	have "bet C R P" using `bet C R P \<and> col B A R \<and> \<not> col B A C` by blast
	have "bet P R C" using betweennesssymmetryE[OF `bet C R P`] .
	have "\<not> col B A C" using `\<not> col B A C` .
	consider "oppo_side G B C A"|"\<not> (oppo_side G B C A)" by blast
	hence "ang_lt A B C D E F"
	proof (cases)
		assume "oppo_side G B C A"
		obtain H where "bet G H A \<and> col B C H \<and> \<not> col B C G" using oppositeside_f[OF `oppo_side G B C A`]  by  blast
		have "bet G H A" using `bet G H A \<and> col B C H \<and> \<not> col B C G` by blast
		have "col B C H" using `bet G H A \<and> col B C H \<and> \<not> col B C G` by blast
		have "bet A H G" using betweennesssymmetryE[OF `bet G H A`] .
		have "ray_on B A A" using ray4 `A = A` `B \<noteq> A` by blast
		have "ray_on B G G" using `ray_on B G G` .
		have "\<not> (col A B H)"
		proof (rule ccontr)
			assume "\<not> (\<not> (col A B H))"
hence "col A B H" by blast
			have "\<not> (B = H)"
			proof (rule ccontr)
				assume "\<not> (B \<noteq> H)"
				hence "B = H" by blast
				have "bet A B G" using `bet A H G` `B = H` by blast
				have "col A B G" using collinear_b `bet A B G` by blast
				have "col G B A" using collinearorder[OF `col A B G`] by blast
				show "False" using `col G B A` `\<not> col G B A` by blast
			qed
			hence "B \<noteq> H" by blast
			have "H \<noteq> B" using inequalitysymmetric[OF `B \<noteq> H`] .
			have "col H B A" using collinearorder[OF `col A B H`] by blast
			have "col H B C" using collinearorder[OF `col B C H`] by blast
			have "col B A C" using collinear4[OF `col H B A` `col H B C` `H \<noteq> B`] .
			have "col A B C" using collinearorder[OF `col B A C`] by blast
			show "False" using `col A B C` `\<not> col A B C` by blast
		qed
		hence "\<not> col A B H" by blast
		have "ang_eq A B H A B H" using equalanglesreflexive[OF `\<not> col A B H`] .
		have "ang_lt A B H A B G" using anglelessthan_b[OF `bet A H G` `ray_on B A A` `ray_on B G G` `ang_eq A B H A B H`] .
		have "ang_eq G B A A B G" using ABCequalsCBA[OF `\<not> col G B A`] .
		have "ang_lt A B H G B A" using angleorderrespectscongruence[OF `ang_lt A B H A B G` `ang_eq G B A A B G`] .
		have "\<not> (col H B A)"
		proof (rule ccontr)
			assume "\<not> (\<not> (col H B A))"
hence "col H B A" by blast
			have "col A B H" using collinearorder[OF `col H B A`] by blast
			show "False" using `col A B H` `\<not> col A B H` by blast
		qed
		hence "\<not> col H B A" by blast
		have "ang_eq H B A A B H" using ABCequalsCBA[OF `\<not> col H B A`] .
		have "ang_lt H B A G B A" using angleorderrespectscongruence2[OF `ang_lt A B H G B A` `ang_eq H B A A B H`] .
		have "ang_lt H B A D E F" using angleorderrespectscongruence[OF `ang_lt H B A G B A` `ang_eq D E F G B A`] .
		have "ang_eq A B H H B A" using ABCequalsCBA[OF `\<not> col A B H`] .
		have "ang_lt A B H D E F" using angleorderrespectscongruence2[OF `ang_lt H B A D E F` `ang_eq A B H H B A`] .
		have "ray_on B A A" using ray4 `A = A` `B \<noteq> A` by blast
		have "same_side G C B A" using `same_side G C B A` .
		have "same_side C G B A" using samesidesymmetric[OF `same_side G C B A`] by blast
		have "bet A H G" using `bet A H G` .
		have "ray_on A G H" using ray4 `bet A H G` `A \<noteq> G` by blast
		have "A = A" using equalityreflexiveE.
		have "col B A A" using collinear_b `A = A` by blast
		have "same_side C H B A" using sameside2[OF `same_side C G B A` `col B A A` `ray_on A G H`] .
		have "\<not> (bet C B H)"
		proof (rule ccontr)
			assume "\<not> (\<not> (bet C B H))"
hence "bet C B H" by blast
			have "B = B" using equalityreflexiveE.
			have "col B A B" using collinear_b `B = B` by blast
			have "oppo_side C B A H" using oppositeside_b[OF `bet C B H` `col B A B` `\<not> col B A C`] .
			have "oppo_side H B A C" using oppositesidesymmetric[OF `oppo_side C B A H`] .
			have "oppo_side C B A C" using planeseparation[OF `same_side C H B A` `oppo_side H B A C`] .
			obtain M where "bet C M C \<and> col B A M \<and> \<not> col B A C" using oppositeside_f[OF `oppo_side C B A C`]  by  blast
			have "bet C M C" using `bet C M C \<and> col B A M \<and> \<not> col B A C` by blast
			have "\<not> (bet C M C)" using betweennessidentityE.
			show "False" using `\<not> (bet C M C)` `bet C M C \<and> col B A M \<and> \<not> col B A C` by blast
		qed
		hence "\<not> (bet C B H)" by blast
		have "col B C H" using `col B C H` .
		have "B = C \<or> B = H \<or> C = H \<or> bet C B H \<or> bet B C H \<or> bet B H C" using collinear_f[OF `col B C H`] .
		consider "B = C"|"B = H"|"C = H"|"bet C B H"|"bet B C H"|"bet B H C" using `B = C \<or> B = H \<or> C = H \<or> bet C B H \<or> bet B C H \<or> bet B H C`  by blast
		hence "ray_on B C H"
		proof (cases)
			assume "B = C"
			have "col A B C" using collinear_b `B = C` by blast
			have "\<not> (\<not> (ray_on B C H))"
			proof (rule ccontr)
				assume "\<not> (\<not> (\<not> (ray_on B C H)))"
hence "\<not> (ray_on B C H)" by blast
				have "\<not> col A B C" using `\<not> col A B C` .
				show "False" using `\<not> col A B C` `col A B C` by blast
			qed
			hence "ray_on B C H" by blast
			thus ?thesis by blast
		next
			assume "B = H"
			have "col B H A" using collinear_b `B = H` by blast
			have "\<not> (\<not> (ray_on B C H))"
			proof (rule ccontr)
				assume "\<not> (\<not> (\<not> (ray_on B C H)))"
hence "\<not> (ray_on B C H)" by blast
				have "\<not> (col B H A)"
				proof (rule ccontr)
					assume "\<not> (\<not> (col B H A))"
hence "col B H A" by blast
					have "col H B A" using collinearorder[OF `col B H A`] by blast
					have "\<not> col H B A" using `\<not> col H B A` .
					show "False" using `\<not> col H B A` `col H B A` by blast
				qed
				hence "\<not> col B H A" by blast
				show "False" using `\<not> col B H A` `col B H A` by blast
			qed
			hence "ray_on B C H" by blast
			thus ?thesis by blast
		next
			assume "C = H"
			have "H = H" using equalityreflexiveE.
			consider "B = H"|"B \<noteq> H" by blast
			hence "ray_on B C H"
			proof (cases)
				assume "B = H"
				have "col B H A" using collinear_b `B = H` by blast
				have "\<not> (\<not> (ray_on B C H))"
				proof (rule ccontr)
					assume "\<not> (\<not> (\<not> (ray_on B C H)))"
hence "\<not> (ray_on B C H)" by blast
					have "\<not> (col B H A)"
					proof (rule ccontr)
						assume "\<not> (\<not> (col B H A))"
hence "col B H A" by blast
						have "col H B A" using collinearorder[OF `col B H A`] by blast
						have "\<not> col H B A" using `\<not> col H B A` .
						show "False" using `\<not> col H B A` `col H B A` by blast
					qed
					hence "\<not> col B H A" by blast
					show "False" using `\<not> col B H A` `col B H A` by blast
				qed
				hence "ray_on B C H" by blast
				thus ?thesis by blast
			next
				assume "B \<noteq> H"
				have "ray_on B H H" using ray4 `H = H` `B \<noteq> H` by blast
				have "ray_on B C H" using `ray_on B H H` `C = H` by blast
				thus ?thesis by blast
			qed
			thus ?thesis by blast
		next
			assume "bet C B H"
			have "\<not> (\<not> (ray_on B C H))"
			proof (rule ccontr)
				assume "\<not> (\<not> (\<not> (ray_on B C H)))"
hence "\<not> (ray_on B C H)" by blast
				have "\<not> (bet C B H)" using `\<not> (bet C B H)` .
				show "False" using `\<not> (bet C B H)` `bet C B H` by blast
			qed
			hence "ray_on B C H" by blast
			thus ?thesis by blast
		next
			assume "bet B C H"
			have "B \<noteq> C" using betweennotequal[OF `bet B C H`] by blast
			have "ray_on B C H" using ray4 `bet B C H` `B \<noteq> C` by blast
			thus ?thesis by blast
		next
			assume "bet B H C"
			have "B \<noteq> C" using betweennotequal[OF `bet B H C`] by blast
			have "ray_on B C H" using ray4 `bet B H C` `B \<noteq> C` by blast
			thus ?thesis by blast
		qed
		have "ang_eq A B C A B C" using equalanglesreflexive[OF `\<not> col A B C`] .
		have "ang_eq A B C A B H" using equalangleshelper[OF `ang_eq A B C A B C` `ray_on B A A` `ray_on B C H`] .
		have "ang_lt A B C D E F" using angleorderrespectscongruence2[OF `ang_lt A B H D E F` `ang_eq A B C A B H`] .
		thus ?thesis by blast
	next
		assume "\<not> (oppo_side G B C A)"
		have "col B A R" using `bet C R P \<and> col B A R \<and> \<not> col B A C` by blast
		have "B = A \<or> B = R \<or> A = R \<or> bet A B R \<or> bet B A R \<or> bet B R A" using collinear_f[OF `col B A R`] .
		consider "B = A"|"B = R"|"A = R"|"bet A B R"|"bet B A R"|"bet B R A" using `B = A \<or> B = R \<or> A = R \<or> bet A B R \<or> bet B A R \<or> bet B R A`  by blast
		hence "ang_lt A B C D E F"
		proof (cases)
			assume "B = A"
			have "\<not> (\<not> (ang_lt A B C D E F))"
			proof (rule ccontr)
				assume "\<not> (\<not> (\<not> (ang_lt A B C D E F)))"
hence "\<not> (ang_lt A B C D E F)" by blast
				have "B \<noteq> A" using `B \<noteq> A` .
				show "False" using `B \<noteq> A` `B = A` by blast
			qed
			hence "ang_lt A B C D E F" by blast
			thus ?thesis by blast
		next
			assume "B = R"
			have "bet G A P" using `bet G A P` .
			have "bet C R P" using betweennesssymmetryE[OF `bet P R C`] .
			have "\<not> (col C P G)"
			proof (rule ccontr)
				assume "\<not> (\<not> (col C P G))"
hence "col C P G" by blast
				have "col C R P" using collinear_b `bet C R P \<and> col B A R \<and> \<not> col B A C` by blast
				have "col C B P" using `col C R P` `B = R` by blast
				have "col G A P" using collinear_b `bet G A P \<and> seg_eq A P G A` by blast
				have "col G P A" using collinearorder[OF `col G A P`] by blast
				have "col G P C" using collinearorder[OF `col C P G`] by blast
				have "G \<noteq> P" using betweennotequal[OF `bet G A P`] by blast
				have "col P C A" using collinear4[OF `col G P C` `col G P A` `G \<noteq> P`] .
				have "col P C B" using collinearorder[OF `col C B P`] by blast
				have "C \<noteq> P" using betweennotequal[OF `bet C R P`] by blast
				have "P \<noteq> C" using inequalitysymmetric[OF `C \<noteq> P`] .
				have "col C A B" using collinear4[OF `col P C A` `col P C B` `P \<noteq> C`] .
				have "col A B C" using collinearorder[OF `col C A B`] by blast
				have "\<not> col A B C" using `\<not> col A B C` .
				show "False" using `\<not> col A B C` `col A B C` by blast
			qed
			hence "\<not> col C P G" by blast
			obtain Q where "bet C Q A \<and> bet G Q R" using Pasch_innerE[OF `bet C R P` `bet G A P` `\<not> col C P G`]  by  blast
			have "bet C Q A" using `bet C Q A \<and> bet G Q R` by blast
			have "bet G Q R" using `bet C Q A \<and> bet G Q R` by blast
			have "bet G Q B" using `bet G Q R` `B = R` by blast
			have "bet B Q G" using betweennesssymmetryE[OF `bet G Q B`] .
			have "B \<noteq> Q" using betweennotequal[OF `bet B Q G`] by blast
			have "B \<noteq> G" using betweennotequal[OF `bet B Q G`] by blast
			have "ray_on B Q G" using ray4 `bet B Q G` `B \<noteq> Q` by blast
			have "ray_on B G Q" using ray5[OF `ray_on B Q G`] .
			have "Q = Q" using equalityreflexiveE.
			have "A = A" using equalityreflexiveE.
			have "C = C" using equalityreflexiveE.
			have "ray_on B A A" using ray4 `A = A` `B \<noteq> A` by blast
			have "ray_on B C C" using ray4 `C = C` `B \<noteq> C` by blast
			have "ray_on B G G" using ray4 `G = G` `B \<noteq> G` by blast
			have "ray_on B Q Q" using ray4 `Q = Q` `B \<noteq> Q` by blast
			have "\<not> col A B G" using `\<not> col A B G` .
			have "seg_eq A Q A Q" using congruencereflexiveE.
			have "seg_eq B Q B Q" using congruencereflexiveE.
			have "seg_eq B A B A" using congruencereflexiveE.
			have "ang_eq A B G A B Q" using equalangles_b[OF `ray_on B A A` `ray_on B G Q` `ray_on B A A` `ray_on B Q Q` `seg_eq B A B A` `seg_eq B Q B Q` `seg_eq A Q A Q` `\<not> col A B G`] .
			have "bet A Q C" using betweennesssymmetryE[OF `bet C Q A`] .
			have "ang_lt A B G A B C" using anglelessthan_b[OF `bet A Q C` `ray_on B A A` `ray_on B C C` `ang_eq A B G A B Q`] .
			have "ang_eq A B G D E F" using `ang_eq A B G D E F` .
			have "ang_eq D E F A B G" using equalanglessymmetric[OF `ang_eq A B G D E F`] .
			have "ang_lt D E F A B C" using angleorderrespectscongruence2[OF `ang_lt A B G A B C` `ang_eq D E F A B G`] .
			have "\<not> (\<not> (ang_lt A B C D E F))"
			proof (rule ccontr)
				assume "\<not> (\<not> (\<not> (ang_lt A B C D E F)))"
hence "\<not> (ang_lt A B C D E F)" by blast
				have "\<not> (ang_lt D E F A B C)" using `\<not> (ang_lt D E F A B C)` .
				show "False" using `\<not> (ang_lt D E F A B C)` `ang_lt D E F A B C` by blast
			qed
			hence "ang_lt A B C D E F" by blast
			thus ?thesis by blast
		next
			assume "A = R"
			have "\<not> (\<not> (ang_lt A B C D E F))"
			proof (rule ccontr)
				assume "\<not> (\<not> (\<not> (ang_lt A B C D E F)))"
hence "\<not> (ang_lt A B C D E F)" by blast
				have "bet P A G" using betweennesssymmetryE[OF `bet G A P`] .
				have "bet P A C" using `bet P R C` `A = R` by blast
				have "G = G" using equalityreflexiveE.
				have "ray_on B G G" using ray4 `G = G` `B \<noteq> G` by blast
				have "A = A" using equalityreflexiveE.
				have "ray_on B A A" using ray4 `A = A` `B \<noteq> A` by blast
				have "C = C" using equalityreflexiveE.
				have "ray_on B C C" using ray4 `C = C` `B \<noteq> C` by blast
				have "ang_eq D E F A B G" using equalanglessymmetric[OF `ang_eq A B G D E F`] .
				have "\<not> (bet A G C)"
				proof (rule ccontr)
					assume "\<not> (\<not> (bet A G C))"
hence "bet A G C" by blast
					have "ang_eq A B G A B G" using equalanglesreflexive[OF `\<not> col A B G`] .
					have "ang_lt A B G A B C" using anglelessthan_b[OF `bet A G C` `ray_on B A A` `ray_on B C C` `ang_eq A B G A B G`] .
					have "ang_lt D E F A B C" using angleorderrespectscongruence2[OF `ang_lt A B G A B C` `ang_eq D E F A B G`] .
					have "\<not> (ang_lt D E F A B C)" using `\<not> (ang_lt D E F A B C)` .
					show "False" using `\<not> (ang_lt D E F A B C)` `ang_lt D E F A B C` by blast
				qed
				hence "\<not> (bet A G C)" by blast
				have "\<not> (bet A C G)"
				proof (rule ccontr)
					assume "\<not> (\<not> (bet A C G))"
hence "bet A C G" by blast
					have "ang_eq A B C A B C" using equalanglesreflexive[OF `\<not> col A B C`] .
					have "ang_lt A B C A B G" using anglelessthan_b[OF `bet A C G` `ray_on B A A` `ray_on B G G` `ang_eq A B C A B C`] .
					have "ang_lt A B C D E F" using angleorderrespectscongruence[OF `ang_lt A B C A B G` `ang_eq D E F A B G`] .
					show "False" using `ang_lt A B C D E F` `\<not> (ang_lt A B C D E F)` by blast
				qed
				hence "\<not> (bet A C G)" by blast
				have "C = G" using outerconnectivity[OF `bet P A C` `bet P A G` `\<not> (bet A C G)` `\<not> (bet A G C)`] .
				have "ang_eq A B C A B C" using equalanglesreflexive[OF `\<not> col A B C`] .
				have "ang_eq A B G A B C" using `ang_eq A B C A B C` `C = G` by blast
				have "ang_eq A B C A B G" using equalanglessymmetric[OF `ang_eq A B G A B C`] .
				have "ang_eq A B C D E F" using equalanglestransitive[OF `ang_eq A B C A B G` `ang_eq A B G D E F`] .
				have "ang_eq A B C D E F" using `ang_eq A B C D E F` .
				show "False" using `ang_eq A B C D E F` `\<not> (ang_eq A B C D E F)` by blast
			qed
			hence "ang_lt A B C D E F" by blast
			thus ?thesis by blast
		next
			assume "bet A B R"
			have "bet R B A" using betweennesssymmetryE[OF `bet A B R`] .
			have "bet C R P" using `bet C R P` .
			have "bet A B R" using betweennesssymmetryE[OF `bet R B A`] .
			have "\<not> (col C P A)"
			proof (rule ccontr)
				assume "\<not> (\<not> (col C P A))"
hence "col C P A" by blast
				have "col C R P" using collinear_b `bet C R P \<and> col B A R \<and> \<not> col B A C` by blast
				have "col C P R" using collinearorder[OF `col C R P`] by blast
				have "C \<noteq> P" using betweennotequal[OF `bet C R P`] by blast
				have "col P A R" using collinear4[OF `col C P A` `col C P R` `C \<noteq> P`] .
				have "col R B A" using collinear_b `bet R B A` by blast
				have "col R A B" using collinearorder[OF `col B A R`] by blast
				have "col R A P" using collinearorder[OF `col P A R`] by blast
				have "R \<noteq> A" using betweennotequal[OF `bet R B A`] by blast
				have "col A B P" using collinear4[OF `col R A B` `col R A P` `R \<noteq> A`] .
				have "col P A B" using collinearorder[OF `col A B P`] by blast
				have "col G A P" using collinear_b `bet G A P \<and> seg_eq A P G A` by blast
				have "col P A G" using collinearorder[OF `col G A P`] by blast
				have "A \<noteq> P" using betweennotequal[OF `bet G A P`] by blast
				have "P \<noteq> A" using inequalitysymmetric[OF `A \<noteq> P`] .
				have "col A B G" using collinear4[OF `col P A B` `col P A G` `P \<noteq> A`] .
				have "\<not> col A B G" using `\<not> col A B G` .
				show "False" using `\<not> col A B G` `col A B G` by blast
			qed
			hence "\<not> col C P A" by blast
			obtain M where "bet A M P \<and> bet C B M" using Pasch_outerE[OF `bet A B R` `bet C R P` `\<not> col C P A`]  by  blast
			have "bet A M P" using `bet A M P \<and> bet C B M` by blast
			have "bet C B M" using `bet A M P \<and> bet C B M` by blast
			have "bet G A P" using `bet G A P` .
			have "bet P A G" using betweennesssymmetryE[OF `bet G A P`] .
			have "bet P M A" using betweennesssymmetryE[OF `bet A M P`] .
			have "bet M A G" using n3_6a[OF `bet P M A` `bet P A G`] .
			have "bet G A M" using betweennesssymmetryE[OF `bet M A G`] .
			have "\<not> (col C M G)"
			proof (rule ccontr)
				assume "\<not> (\<not> (col C M G))"
hence "col C M G" by blast
				have "bet P M A" using betweennesssymmetryE[OF `bet A M P`] .
				have "bet P A G" using betweennesssymmetryE[OF `bet G A P`] .
				have "bet P M G" using n3_6b[OF `bet P M A` `bet P A G`] .
				have "col P M G" using collinear_b `bet P M G` by blast
				have "col M G P" using collinearorder[OF `col P M G`] by blast
				have "col M G C" using collinearorder[OF `col C M G`] by blast
				have "M \<noteq> G" using betweennotequal[OF `bet M A G`] by blast
				have "col G P C" using collinear4[OF `col M G P` `col M G C` `M \<noteq> G`] .
				have "col P A G" using collinear_b `bet P A G` by blast
				have "col G P A" using collinearorder[OF `col P A G`] by blast
				have "P \<noteq> G" using betweennotequal[OF `bet P A G`] by blast
				have "G \<noteq> P" using inequalitysymmetric[OF `P \<noteq> G`] .
				have "col P C A" using collinear4[OF `col G P C` `col G P A` `G \<noteq> P`] .
				have "col C P A" using collinearorder[OF `col P C A`] by blast
				have "\<not> col C P A" using `\<not> col C P A` .
				show "False" using `\<not> col C P A` `col C P A` by blast
			qed
			hence "\<not> col C M G" by blast
			obtain Q where "bet C Q A \<and> bet G Q B" using Pasch_innerE[OF `bet C B M` `bet G A M` `\<not> col C M G`]  by  blast
			have "bet C Q A" using `bet C Q A \<and> bet G Q B` by blast
			have "bet G Q B" using `bet C Q A \<and> bet G Q B` by blast
			have "bet B Q G" using betweennesssymmetryE[OF `bet G Q B`] .
			have "B \<noteq> Q" using betweennotequal[OF `bet B Q G`] by blast
			have "B \<noteq> G" using betweennotequal[OF `bet B Q G`] by blast
			have "ray_on B Q G" using ray4 `bet B Q G` `B \<noteq> Q` by blast
			have "ray_on B G Q" using ray5[OF `ray_on B Q G`] .
			have "Q = Q" using equalityreflexiveE.
			have "A = A" using equalityreflexiveE.
			have "C = C" using equalityreflexiveE.
			have "ray_on B A A" using ray4 `A = A` `B \<noteq> A` by blast
			have "ray_on B C C" using ray4 `C = C` `B \<noteq> C` by blast
			have "ray_on B G G" using ray4 `G = G` `B \<noteq> G` by blast
			have "ray_on B Q Q" using ray4 `Q = Q` `B \<noteq> Q` by blast
			have "\<not> col A B G" using `\<not> col A B G` .
			have "seg_eq A Q A Q" using congruencereflexiveE.
			have "seg_eq B Q B Q" using congruencereflexiveE.
			have "seg_eq B A B A" using congruencereflexiveE.
			have "ang_eq A B G A B Q" using equalangles_b[OF `ray_on B A A` `ray_on B G Q` `ray_on B A A` `ray_on B Q Q` `seg_eq B A B A` `seg_eq B Q B Q` `seg_eq A Q A Q` `\<not> col A B G`] .
			have "bet A Q C" using betweennesssymmetryE[OF `bet C Q A`] .
			have "ang_lt A B G A B C" using anglelessthan_b[OF `bet A Q C` `ray_on B A A` `ray_on B C C` `ang_eq A B G A B Q`] .
			have "ang_eq A B G D E F" using `ang_eq A B G D E F` .
			have "ang_eq D E F A B G" using equalanglessymmetric[OF `ang_eq A B G D E F`] .
			have "ang_lt D E F A B C" using angleorderrespectscongruence2[OF `ang_lt A B G A B C` `ang_eq D E F A B G`] .
			have "\<not> (\<not> (ang_lt A B C D E F))"
			proof (rule ccontr)
				assume "\<not> (\<not> (\<not> (ang_lt A B C D E F)))"
hence "\<not> (ang_lt A B C D E F)" by blast
				have "\<not> (ang_lt D E F A B C)" using `\<not> (ang_lt D E F A B C)` .
				show "False" using `\<not> (ang_lt D E F A B C)` `ang_lt D E F A B C` by blast
			qed
			hence "ang_lt A B C D E F" by blast
			thus ?thesis by blast
		next
			assume "bet B A R"
			have "\<not> (col P C B)"
			proof (rule ccontr)
				assume "\<not> (\<not> (col P C B))"
hence "col P C B" by blast
				have "col B A R" using collinear_b[OF `B = A \<or> B = R \<or> A = R \<or> bet A B R \<or> bet B A R \<or> bet B R A`] .
				have "col P R C" using collinear_b `bet P R C` by blast
				have "col P C R" using collinearorder[OF `col P R C`] by blast
				have "P \<noteq> C" using betweennotequal[OF `bet P R C`] by blast
				have "col C B R" using collinear4[OF `col P C B` `col P C R` `P \<noteq> C`] .
				have "col R B C" using collinearorder[OF `col C B R`] by blast
				have "col R B A" using collinearorder[OF `col B A R`] by blast
				have "B \<noteq> R" using betweennotequal[OF `bet B A R`] by blast
				have "R \<noteq> B" using inequalitysymmetric[OF `B \<noteq> R`] .
				have "col B C A" using collinear4[OF `col R B C` `col R B A` `R \<noteq> B`] .
				have "col A B C" using collinearorder[OF `col B C A`] by blast
				have "\<not> col A B C" using `\<not> col A B C` .
				show "False" using `\<not> col A B C` `col A B C` by blast
			qed
			hence "\<not> col P C B" by blast
			obtain Q where "bet B Q C \<and> bet P A Q" using Pasch_outerE[OF `bet B A R` `bet P R C` `\<not> col P C B`]  by  blast
			have "bet B Q C" using `bet B Q C \<and> bet P A Q` by blast
			have "col B C Q" using collinear_b `bet B Q C \<and> bet P A Q` by blast
			have "\<not> (G = Q)"
			proof (rule ccontr)
				assume "\<not> (G \<noteq> Q)"
				hence "G = Q" by blast
				have "bet B G C" using `bet B Q C` `G = Q` by blast
				have "ray_on B C G" using ray4 `bet B G C` `B \<noteq> C` by blast
				have "ray_on B A A" using ray4 `A = A` `B \<noteq> A` by blast
				have "ray_on B G G" using ray4 `G = G` `B \<noteq> G` by blast
				have "seg_eq A G A G" using congruencereflexiveE.
				have "seg_eq B G B G" using congruencereflexiveE.
				have "seg_eq B A B A" using congruencereflexiveE.
				have "\<not> col A B G" using `\<not> col A B G` .
				have "ang_eq A B G A B C" using equalangles_b[OF `ray_on B A A` `ray_on B G G` `ray_on B A A` `ray_on B C G` `seg_eq B A B A` `seg_eq B G B G` `seg_eq A G A G` `\<not> col A B G`] .
				have "ang_eq A B C A B G" using equalanglessymmetric[OF `ang_eq A B G A B C`] .
				have "ang_eq A B G D E F" using `ang_eq A B G D E F` .
				have "ang_eq A B C D E F" using equalanglestransitive[OF `ang_eq A B C A B G` `ang_eq A B G D E F`] .
				have "\<not> (ang_eq A B C D E F)" using `\<not> (ang_eq A B C D E F)` .
				show "False" using `\<not> (ang_eq A B C D E F)` `ang_eq A B C D E F` by blast
			qed
			hence "G \<noteq> Q" by blast
			have "\<not> (col B C G)"
			proof (rule ccontr)
				assume "\<not> (\<not> (col B C G))"
hence "col B C G" by blast
				have "bet P A Q" using `bet B Q C \<and> bet P A Q` by blast
				have "bet P A G" using betweennesssymmetryE[OF `bet G A P`] .
				have "ray_on A G Q" using ray_b[OF `bet P A Q` `bet P A G`] .
				have "col A G Q" using rayimpliescollinear[OF `ray_on A G Q`] .
				have "col C B G" using collinearorder[OF `col B C G`] by blast
				have "col C B Q" using collinearorder[OF `col B C Q`] by blast
				have "B \<noteq> C" using betweennotequal[OF `bet B Q C`] by blast
				have "C \<noteq> B" using inequalitysymmetric[OF `B \<noteq> C`] .
				have "B = B" using equalityreflexiveE.
				have "col C B B" using collinear_b `B = B` by blast
				have "col G Q B" using collinear5[OF `C \<noteq> B` `col C B G` `col C B Q` `col C B B`] .
				have "col Q G B" using collinearorder[OF `col G Q B`] by blast
				have "col Q G A" using collinearorder[OF `col A G Q`] by blast
				have "Q \<noteq> G" using inequalitysymmetric[OF `G \<noteq> Q`] .
				have "col G B A" using collinear4[OF `col Q G B` `col Q G A` `Q \<noteq> G`] .
				have "col A B G" using collinearorder[OF `col G B A`] by blast
				show "False" using `col A B G` `\<not> col A B G` by blast
			qed
			hence "\<not> col B C G" by blast
			have "\<not> (bet A Q G)"
			proof (rule ccontr)
				assume "\<not> (\<not> (bet A Q G))"
hence "bet A Q G" by blast
				have "bet G Q A" using betweennesssymmetryE[OF `bet A Q G`] .
				have "oppo_side G B C A" using oppositeside_b[OF `bet G Q A` `col B C Q` `\<not> col B C G`] .
				show "False" using `oppo_side G B C A` `\<not> (oppo_side G B C A)` by blast
			qed
			hence "\<not> (bet A Q G)" by blast
			have "ray_on B C Q" using ray4 `bet B Q C \<and> bet P A Q` `B \<noteq> C` by blast
			have "ray_on B A A" using ray4 `A = A` `B \<noteq> A` by blast
			have "\<not> (bet A G Q)"
			proof (rule ccontr)
				assume "\<not> (\<not> (bet A G Q))"
hence "bet A G Q" by blast
				have "ang_eq A B G A B G" using equalanglesreflexive[OF `\<not> col A B G`] .
				have "ang_lt A B G A B C" using anglelessthan_b[OF `bet A G Q` `ray_on B A A` `ray_on B C Q` `ang_eq A B G A B G`] .
				have "ang_eq D E F A B G" using equalanglessymmetric[OF `ang_eq A B G D E F`] .
				have "ang_lt D E F A B C" using angleorderrespectscongruence2[OF `ang_lt A B G A B C` `ang_eq D E F A B G`] .
				show "False" using `ang_lt D E F A B C` `\<not> (ang_lt D E F A B C)` by blast
			qed
			hence "\<not> (bet A G Q)" by blast
			have "bet P A Q" using `bet B Q C \<and> bet P A Q` by blast
			have "bet P A G" using betweennesssymmetryE[OF `bet G A P`] .
			have "\<not> (bet A G Q)" using `\<not> (bet A G Q)` .
			have "\<not> (bet A Q G)" using `\<not> (bet A Q G)` .
			have "G = Q" using outerconnectivity[OF `bet P A G` `bet P A Q` `\<not> (bet A G Q)` `\<not> (bet A Q G)`] .
			have "\<not> (\<not> (ang_lt A B C D E F))"
			proof (rule ccontr)
				assume "\<not> (\<not> (\<not> (ang_lt A B C D E F)))"
hence "\<not> (ang_lt A B C D E F)" by blast
				have "G \<noteq> Q" using `G \<noteq> Q` .
				show "False" using `G \<noteq> Q` `G = Q` by blast
			qed
			hence "ang_lt A B C D E F" by blast
			thus ?thesis by blast
		next
			assume "bet B R A"
			have "\<not> (\<not> (ang_lt A B C D E F))"
			proof (rule ccontr)
				assume "\<not> (\<not> (\<not> (ang_lt A B C D E F)))"
hence "\<not> (ang_lt A B C D E F)" by blast
				have "bet P A G" using betweennesssymmetryE[OF `bet G A P`] .
				have "bet B R A" using `bet B R A` .
				have "\<not> (col P G B)"
				proof (rule ccontr)
					assume "\<not> (\<not> (col P G B))"
hence "col P G B" by blast
					have "col P A G" using collinear_b `bet P A G` by blast
					have "col P G A" using collinearorder[OF `col P A G`] by blast
					have "P \<noteq> G" using betweennotequal[OF `bet P A G`] by blast
					have "col G B A" using collinear4[OF `col P G B` `col P G A` `P \<noteq> G`] .
					have "col A B G" using collinearorder[OF `col G B A`] by blast
					have "\<not> col A B G" using `\<not> col A B G` .
					show "False" using `\<not> col A B G` `col A B G` by blast
				qed
				hence "\<not> col P G B" by blast
				obtain Q where "bet B Q G \<and> bet P R Q" using Pasch_outerE[OF `bet B R A` `bet P A G` `\<not> col P G B`]  by  blast
				have "bet B Q G" using `bet B Q G \<and> bet P R Q` by blast
				have "B \<noteq> Q" using betweennotequal[OF `bet B Q G`] by blast
				have "ray_on B Q G" using ray4 `bet B Q G \<and> bet P R Q` `B \<noteq> Q` by blast
				have "\<not> (bet R C Q)"
				proof (rule ccontr)
					assume "\<not> (\<not> (bet R C Q))"
hence "bet R C Q" by blast
					have "ray_on B A R" using ray4 `bet B R A` `B \<noteq> A` by blast
					have "ray_on B G Q" using ray4 `bet B Q G \<and> bet P R Q` `B \<noteq> G` by blast
					have "ang_eq A B C A B C" using equalanglesreflexive[OF `\<not> col A B C`] .
					have "ang_lt A B C A B G" using anglelessthan_b[OF `bet R C Q` `ray_on B A R` `ray_on B G Q` `ang_eq A B C A B C`] .
					have "ang_eq A B G D E F" using `ang_eq A B G D E F` .
					have "ang_eq D E F A B G" using equalanglessymmetric[OF `ang_eq A B G D E F`] .
					have "ang_lt A B C D E F" using angleorderrespectscongruence[OF `ang_lt A B C A B G` `ang_eq D E F A B G`] .
					show "False" using `ang_lt A B C D E F` `\<not> (ang_lt A B C D E F)` by blast
				qed
				hence "\<not> (bet R C Q)" by blast
				have "\<not> (bet R Q C)"
				proof (rule ccontr)
					assume "\<not> (\<not> (bet R Q C))"
hence "bet R Q C" by blast
					have "A = A" using equalityreflexiveE.
					have "ray_on B A A" using ray4 `A = A` `B \<noteq> A` by blast
					have "ray_on B Q G" using ray4 `bet B Q G \<and> bet P R Q` `B \<noteq> Q` by blast
					have "G = G" using equalityreflexiveE.
					have "ray_on B G G" using ray4 `G = G` `B \<noteq> G` by blast
					have "seg_eq B A B A" using congruencereflexiveE.
					have "seg_eq B G B G" using congruencereflexiveE.
					have "seg_eq A G A G" using congruencereflexiveE.
					have "\<not> col A B G" using `\<not> col A B G` .
					have "ang_eq A B G A B Q" using equalangles_b[OF `ray_on B A A` `ray_on B G G` `ray_on B A A` `ray_on B Q G` `seg_eq B A B A` `seg_eq B G B G` `seg_eq A G A G` `\<not> col A B G`] .
					have "ray_on B A R" using ray4 `bet B R A` `B \<noteq> A` by blast
					have "C = C" using equalityreflexiveE.
					have "ray_on B C C" using ray4 `C = C` `B \<noteq> C` by blast
					have "ang_lt A B G A B C" using anglelessthan_b[OF `bet R Q C` `ray_on B A R` `ray_on B C C` `ang_eq A B G A B Q`] .
					have "ang_eq D E F A B G" using equalanglessymmetric[OF `ang_eq A B G D E F`] .
					have "ang_lt D E F A B C" using angleorderrespectscongruence2[OF `ang_lt A B G A B C` `ang_eq D E F A B G`] .
					have "\<not> (ang_lt D E F A B C)" using `\<not> (ang_lt D E F A B C)` .
					show "False" using `\<not> (ang_lt D E F A B C)` `ang_lt D E F A B C` by blast
				qed
				hence "\<not> (bet R Q C)" by blast
				have "bet P R Q" using `bet B Q G \<and> bet P R Q` by blast
				have "bet P R C" using `bet P R C` .
				have "Q = C" using outerconnectivity[OF `bet P R Q` `bet P R C` `\<not> (bet R Q C)` `\<not> (bet R C Q)`] .
				have "C = C" using equalityreflexiveE.
				have "ray_on B C C" using ray4 `C = C` `B \<noteq> C` by blast
				have "ray_on B C G" using `ray_on B Q G` `Q = C` by blast
				have "A = A" using equalityreflexiveE.
				have "ray_on B A A" using ray4 `A = A` `B \<noteq> A` by blast
				have "G = G" using equalityreflexiveE.
				have "ray_on B G G" using ray4 `G = G` `B \<noteq> G` by blast
				have "seg_eq B A B A" using congruencereflexiveE.
				have "seg_eq B G B G" using congruencereflexiveE.
				have "seg_eq A G A G" using congruencereflexiveE.
				have "ang_eq A B C A B G" using equalangles_b[OF `ray_on B A A` `ray_on B C G` `ray_on B A A` `ray_on B G G` `seg_eq B A B A` `seg_eq B G B G` `seg_eq A G A G` `\<not> col A B C`] .
				have "ang_eq A B C D E F" using equalanglestransitive[OF `ang_eq A B C A B G` `ang_eq A B G D E F`] .
				have "ang_eq A B C D E F" using `ang_eq A B C D E F` .
				show "False" using `ang_eq A B C D E F` `\<not> (ang_eq A B C D E F)` by blast
			qed
			hence "ang_lt A B C D E F" by blast
			thus ?thesis by blast
		qed
		thus ?thesis by blast
	qed
	thus ?thesis by blast
qed

end