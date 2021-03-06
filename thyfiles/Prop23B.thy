theory Prop23B
	imports n8_2 n8_3 n9_5 ABCequalsCBA Euclid4 Geometry Prop04 Prop11B Prop12 Prop23 angledistinct betweennotequal collinear4 collinear5 collinearorder collinearright congruenceflip doublereverse equalanglesNC equalanglesflip equalangleshelper equalanglesreflexive equalanglessymmetric equalanglestransitive inequalitysymmetric layoff ray4 ray5 rayimpliescollinear raystrict rightangleNC supplements
begin

theorem(in euclidean_geometry) Prop23B:
	assumes 
		"A \<noteq> B"
		"\<not> col D C E"
		"\<not> col A B P"
	shows "\<exists> G S. ray_on A B G \<and> ang_eq S A G D C E \<and> oppo_side S A B P"
proof -
	have "B \<noteq> A" using inequalitysymmetric[OF `A \<noteq> B`] .
	obtain F G where "ray_on A B G \<and> ang_eq F A G D C E" using Prop23[OF `A \<noteq> B` `\<not> col D C E`]  by  blast
	have "ray_on A B G" using `ray_on A B G \<and> ang_eq F A G D C E` by blast
	have "A \<noteq> G" using raystrict[OF `ray_on A B G`] .
	have "ang_eq F A G D C E" using `ray_on A B G \<and> ang_eq F A G D C E` by blast
	have "\<not> (col A B F)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col A B F))"
hence "col A B F" by blast
		have "ang_eq D C E F A G" using equalanglessymmetric[OF `ang_eq F A G D C E`] .
		have "\<not> col F A G" using equalanglesNC[OF `ang_eq D C E F A G`] .
		have "col A B G" using rayimpliescollinear[OF `ray_on A B G`] .
		have "col B F G" using collinear4[OF `col A B F` `col A B G` `A \<noteq> B`] .
		have "col B F A" using collinearorder[OF `col A B F`] by blast
		have "\<not> (F = B)"
		proof (rule ccontr)
			assume "\<not> (F \<noteq> B)"
			hence "F = B" by blast
			have "ray_on A F G" using `ray_on A B G` `F = B` by blast
			have "col A F G" using rayimpliescollinear[OF `ray_on A F G`] .
			have "col F A G" using collinearorder[OF `col A F G`] by blast
			show "False" using `col F A G` `\<not> col F A G` by blast
		qed
		hence "F \<noteq> B" by blast
		have "B \<noteq> F" using inequalitysymmetric[OF `F \<noteq> B`] .
		have "col F A G" using collinear4[OF `col B F A` `col B F G` `B \<noteq> F`] .
		show "False" using `col F A G` `\<not> col F A G` by blast
	qed
	hence "\<not> col A B F" by blast
	obtain H where "perp_at F H A B H" using Prop12[OF `A \<noteq> B` `\<not> col A B F`]  by  blast
	obtain J where "col F H H \<and> col A B H \<and> col A B J \<and> ang_right J H F" using perpat_f[OF `perp_at F H A B H`]  by  blast
	have "col A B H" using `col F H H \<and> col A B H \<and> col A B J \<and> ang_right J H F` by blast
	have "ang_right J H F" using `col F H H \<and> col A B H \<and> col A B J \<and> ang_right J H F` by blast
	have "\<not> col J H F" using rightangleNC[OF `ang_right J H F`] .
	have "\<not> (F = H)"
	proof (rule ccontr)
		assume "\<not> (F \<noteq> H)"
		hence "F = H" by blast
		have "col A B F" using `col A B H` `F = H` by blast
		have "\<not> col A B F" using `\<not> col A B F` .
		show "False" using `\<not> col A B F` `col A B F` by blast
	qed
	hence "F \<noteq> H" by blast
	have "\<not> (J = H)"
	proof (rule ccontr)
		assume "\<not> (J \<noteq> H)"
		hence "J = H" by blast
		have "col J H F" using collinear_b `J = H` by blast
		show "False" using `col J H F` `\<not> col J H F` by blast
	qed
	hence "J \<noteq> H" by blast
	have "H \<noteq> J" using inequalitysymmetric[OF `J \<noteq> H`] .
	obtain T where "bet J H T \<and> seg_eq H T H J" using extensionE[OF `J \<noteq> H` `H \<noteq> J`]  by  blast
	have "bet J H T" using `bet J H T \<and> seg_eq H T H J` by blast
	have "col J H T" using collinear_b `bet J H T \<and> seg_eq H T H J` by blast
	have "col A B J" using `col F H H \<and> col A B H \<and> col A B J \<and> ang_right J H F` by blast
	have "col A B H" using `col A B H` .
	have "col B J H" using collinear4[OF `col A B J` `col A B H` `A \<noteq> B`] .
	have "J \<noteq> T" using betweennotequal[OF `bet J H T`] by blast
	have "col H J B" using collinearorder[OF `col B J H`] by blast
	have "col H J T" using collinearorder[OF `col J H T`] by blast
	have "J \<noteq> H" using betweennotequal[OF `bet J H T`] by blast
	have "H \<noteq> J" using inequalitysymmetric[OF `J \<noteq> H`] .
	have "col J B T" using collinear4[OF `col H J B` `col H J T` `H \<noteq> J`] .
	have "col J T B" using collinearorder[OF `col J B T`] by blast
	have "col B A J" using collinearorder[OF `col A B J`] by blast
	have "col B A H" using collinearorder[OF `col A B H`] by blast
	have "col A J H" using collinear4[OF `col B A J` `col B A H` `B \<noteq> A`] .
	have "col H J A" using collinearorder[OF `col A J H`] by blast
	have "col J A T" using collinear4[OF `col H J A` `col H J T` `H \<noteq> J`] .
	have "col J T A" using collinearorder[OF `col J A T`] by blast
	have "\<not> (col J T P)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col J T P))"
hence "col J T P" by blast
		have "col J T P" using `col J T P` .
		have "col A B P" using collinear5[OF `J \<noteq> T` `col J T A` `col J T B` `col J T P`] .
		show "False" using `col A B P` `\<not> col A B P` by blast
	qed
	hence "\<not> col J T P" by blast
	obtain Q where "ang_right J H Q \<and> oppo_side Q J T P" using Prop11B[OF `bet J H T` `\<not> col J T P`]  by  blast
	have "ang_right J H Q" using `ang_right J H Q \<and> oppo_side Q J T P` by blast
	have "\<not> col J H Q" using rightangleNC[OF `ang_right J H Q`] .
	have "\<not> (H = Q)"
	proof (rule ccontr)
		assume "\<not> (H \<noteq> Q)"
		hence "H = Q" by blast
		have "col J H Q" using collinear_b `H = Q` by blast
		show "False" using `col J H Q` `\<not> col J H Q` by blast
	qed
	hence "H \<noteq> Q" by blast
	have "\<not> (H = F)"
	proof (rule ccontr)
		assume "\<not> (H \<noteq> F)"
		hence "H = F" by blast
		have "col J H F" using collinear_b `H = F` by blast
		show "False" using `col J H F` `\<not> col J H F` by blast
	qed
	hence "H \<noteq> F" by blast
	obtain S where "ray_on H Q S \<and> seg_eq H S H F" using layoff[OF `H \<noteq> Q` `H \<noteq> F`]  by  blast
	have "ray_on H Q S" using `ray_on H Q S \<and> seg_eq H S H F` by blast
	have "seg_eq H S H F" using `ray_on H Q S \<and> seg_eq H S H F` by blast
	have "F = F" using equalityreflexiveE.
	have "D \<noteq> C" using angledistinct[OF `ang_eq F A G D C E`] by blast
	have "C \<noteq> D" using inequalitysymmetric[OF `D \<noteq> C`] .
	have "C \<noteq> E" using angledistinct[OF `ang_eq F A G D C E`] by blast
	have "ang_right J H F" using `ang_right J H F` .
	have "col J H A" using collinearorder[OF `col A J H`] by blast
	have "ang_right J H Q" using `ang_right J H Q` .
	have "ang_right J H S" using n8_3[OF `ang_right J H Q` `ray_on H Q S`] .
	have "ang_right S H J" using n8_2[OF `ang_right J H S`] .
	have "ang_eq J H F J H S" using Euclid4[OF `ang_right J H F` `ang_right J H S`] .
	have "S = S" using equalityreflexiveE.
	have "H \<noteq> S" using angledistinct[OF `ang_eq J H F J H S`] by blast
	consider "A = H"|"A \<noteq> H" by blast
	hence "ang_eq F A G S A G"
	proof (cases)
		assume "A = H"
		have "A \<noteq> G" using `A \<noteq> G` .
		have "ang_right J A F" using `ang_right J H F` `A = H` by blast
		have "ang_right J A S" using `ang_right J H S` `A = H` by blast
		have "col A B H" using `col A B H` .
		have "col A B J" using `col A B J` .
		have "col A B G" using rayimpliescollinear[OF `ray_on A B G`] .
		have "col J H G" using collinear5[OF `A \<noteq> B` `col A B J` `col A B H` `col A B G`] .
		have "col J A G" using `col J H G` `A = H` by blast
		have "ang_right J A F" using `ang_right J A F` .
		have "G \<noteq> A" using inequalitysymmetric[OF `A \<noteq> G`] .
		have "ang_right G A F" using collinearright[OF `ang_right J A F` `col J A G` `G \<noteq> A`] .
		have "ang_right F A G" using n8_2[OF `ang_right G A F`] .
		have "ang_right J A S" using `ang_right J A S` .
		have "ang_right G A S" using collinearright[OF `ang_right J A S` `col J A G` `G \<noteq> A`] .
		have "ang_right S A G" using n8_2[OF `ang_right G A S`] .
		have "ang_eq F A G S A G" using Euclid4[OF `ang_right F A G` `ang_right S A G`] .
		thus ?thesis by blast
	next
		assume "A \<noteq> H"
		have "seg_eq F H S H" using doublereverse[OF `seg_eq H S H F`] by blast
		have "ang_right J H F" using `ang_right J H F` .
		have "ang_right A H F" using collinearright[OF `ang_right J H F` `col J H A` `A \<noteq> H`] .
		have "ang_right F H A" using n8_2[OF `ang_right A H F`] .
		have "ang_right S H J" using `ang_right S H J` .
		have "ang_right J H S" using n8_2[OF `ang_right S H J`] .
		have "ang_right A H S" using collinearright[OF `ang_right J H S` `col J H A` `A \<noteq> H`] .
		have "ang_eq A H F A H S" using Euclid4[OF `ang_right A H F` `ang_right A H S`] .
		have "\<not> col F H A" using rightangleNC[OF `ang_right F H A`] .
		have "ang_eq F H A A H F" using ABCequalsCBA[OF `\<not> col F H A`] .
		have "ang_eq F H A A H S" using equalanglestransitive[OF `ang_eq F H A A H F` `ang_eq A H F A H S`] .
		have "\<not> col A H S" using rightangleNC[OF `ang_right A H S`] .
		have "ang_eq A H S S H A" using ABCequalsCBA[OF `\<not> col A H S`] .
		have "ang_eq F H A S H A" using equalanglestransitive[OF `ang_eq F H A A H S` `ang_eq A H S S H A`] .
		have "seg_eq H F H S" using congruenceflip[OF `seg_eq F H S H`] by blast
		have "seg_eq H A H A" using congruencereflexiveE.
		have "\<not> (col S H A)"
		proof (rule ccontr)
			assume "\<not> (\<not> (col S H A))"
hence "col S H A" by blast
			have "col A H S" using collinearorder[OF `col S H A`] by blast
			show "False" using `col A H S` `\<not> col A H S` by blast
		qed
		hence "\<not> col S H A" by blast
		have "seg_eq F A S A \<and> ang_eq H F A H S A \<and> ang_eq H A F H A S" using Prop04[OF `seg_eq H F H S` `seg_eq H A H A` `ang_eq F H A S H A`] .
		have "ang_eq H A F H A S" using `seg_eq F A S A \<and> ang_eq H F A H S A \<and> ang_eq H A F H A S` by blast
		have "\<not> (col F A H)"
		proof (rule ccontr)
			assume "\<not> (\<not> (col F A H))"
hence "col F A H" by blast
			have "col F H A" using collinearorder[OF `col F A H`] by blast
			show "False" using `col F H A` `\<not> col F H A` by blast
		qed
		hence "\<not> col F A H" by blast
		have "ang_eq F A H H A F" using ABCequalsCBA[OF `\<not> col F A H`] .
		have "\<not> (col H A S)"
		proof (rule ccontr)
			assume "\<not> (\<not> (col H A S))"
hence "col H A S" by blast
			have "col S H A" using collinearorder[OF `col H A S`] by blast
			show "False" using `col S H A` `\<not> col S H A` by blast
		qed
		hence "\<not> col H A S" by blast
		have "ang_eq H A S S A H" using ABCequalsCBA[OF `\<not> col H A S`] .
		have "ang_eq F A H H A S" using equalanglestransitive[OF `ang_eq F A H H A F` `ang_eq H A F H A S`] .
		have "ang_eq F A H S A H" using equalanglestransitive[OF `ang_eq F A H H A S` `ang_eq H A S S A H`] .
		have "ray_on A B G" using `ray_on A B G` .
		have "col A B H" using `col A B H` .
		have "A = A" using equalityreflexiveE.
		have "col A B A" using collinear_b `A = A` by blast
		have "col A B G" using rayimpliescollinear[OF `ray_on A B G`] .
		consider "G = H"|"G \<noteq> H" by blast
		hence "col G H A"
		proof (cases)
			assume "G = H"
			have "col G H A" using collinear_b `G = H` by blast
			thus ?thesis by blast
		next
			assume "G \<noteq> H"
			have "col G H A" using collinear5[OF `A \<noteq> B` `col A B G` `col A B H` `col A B A`] .
			thus ?thesis by blast
		qed
		have "F \<noteq> A" using angledistinct[OF `ang_eq F A G D C E`] by blast
		have "A \<noteq> F" using inequalitysymmetric[OF `F \<noteq> A`] .
		have "ray_on A F F" using ray4 `F = F` `A \<noteq> F` by blast
		have "S \<noteq> A" using angledistinct[OF `ang_eq A H S S H A`] by blast
		have "A \<noteq> S" using inequalitysymmetric[OF `S \<noteq> A`] .
		have "ray_on A S S" using ray4 `S = S` `A \<noteq> S` by blast
		have "G = H \<or> G = A \<or> H = A \<or> bet H G A \<or> bet G H A \<or> bet G A H" using collinear_f[OF `col G H A`] .
		consider "G = H"|"G = A"|"H = A"|"bet H G A"|"bet G H A"|"bet G A H" using `G = H \<or> G = A \<or> H = A \<or> bet H G A \<or> bet G H A \<or> bet G A H`  by blast
		hence "ang_eq F A G S A G"
		proof (cases)
			assume "G = H"
			have "\<not> (\<not> (ang_eq F A G S A G))"
			proof (rule ccontr)
				assume "\<not> (\<not> (\<not> (ang_eq F A G S A G)))"
hence "\<not> (ang_eq F A G S A G)" by blast
				have "ang_eq F A G S A G" using `ang_eq F A H S A H` `G = H` `G = H` by blast
				show "False" using `ang_eq F A G S A G` `\<not> (ang_eq F A G S A G)` by blast
			qed
			hence "ang_eq F A G S A G" by blast
			thus ?thesis by blast
		next
			assume "G = A"
			have "\<not> (\<not> (ang_eq F A G S A G))"
			proof (rule ccontr)
				assume "\<not> (\<not> (\<not> (ang_eq F A G S A G)))"
hence "\<not> (ang_eq F A G S A G)" by blast
				have "ray_on A B G" using `ray_on A B G` .
				have "A \<noteq> G" using raystrict[OF `ray_on A B G`] .
				have "G \<noteq> A" using inequalitysymmetric[OF `A \<noteq> G`] .
				show "False" using `G \<noteq> A` `G = A` by blast
			qed
			hence "ang_eq F A G S A G" by blast
			thus ?thesis by blast
		next
			assume "H = A"
			have "\<not> (\<not> (ang_eq F A G S A G))"
			proof (rule ccontr)
				assume "\<not> (\<not> (\<not> (ang_eq F A G S A G)))"
hence "\<not> (ang_eq F A G S A G)" by blast
				have "H \<noteq> A" using inequalitysymmetric[OF `A \<noteq> H`] .
				show "False" using `H \<noteq> A` `H = A` by blast
			qed
			hence "ang_eq F A G S A G" by blast
			thus ?thesis by blast
		next
			assume "bet H G A"
			have "bet A G H" using betweennesssymmetryE[OF `bet H G A`] .
			have "ray_on A H G" using ray4 `bet A G H` `A \<noteq> H` by blast
			have "ang_eq F A H F A H" using equalanglesreflexive[OF `\<not> col F A H`] .
			have "\<not> (col S A H)"
			proof (rule ccontr)
				assume "\<not> (\<not> (col S A H))"
hence "col S A H" by blast
				have "col S H A" using collinearorder[OF `col S A H`] by blast
				show "False" using `col S H A` `\<not> col S H A` by blast
			qed
			hence "\<not> col S A H" by blast
			have "ang_eq S A H S A H" using equalanglesreflexive[OF `\<not> col S A H`] .
			have "ang_eq F A H F A G" using equalangleshelper[OF `ang_eq F A H F A H` `ray_on A F F` `ray_on A H G`] .
			have "ang_eq S A H S A G" using equalangleshelper[OF `ang_eq S A H S A H` `ray_on A S S` `ray_on A H G`] .
			have "ang_eq F A G F A H" using equalanglessymmetric[OF `ang_eq F A H F A G`] .
			have "ang_eq F A G S A H" using equalanglestransitive[OF `ang_eq F A G F A H` `ang_eq F A H S A H`] .
			have "ang_eq F A G S A G" using equalanglestransitive[OF `ang_eq F A G S A H` `ang_eq S A H S A G`] .
			thus ?thesis by blast
		next
			assume "bet G H A"
			have "bet A H G" using betweennesssymmetryE[OF `bet G H A`] .
			have "ray_on A H G" using ray4 `bet A H G` `A \<noteq> H` by blast
			have "ang_eq F A H F A H" using equalanglesreflexive[OF `\<not> col F A H`] .
			have "\<not> (col S A H)"
			proof (rule ccontr)
				assume "\<not> (\<not> (col S A H))"
hence "col S A H" by blast
				have "col S H A" using collinearorder[OF `col S A H`] by blast
				show "False" using `col S H A` `\<not> col S H A` by blast
			qed
			hence "\<not> col S A H" by blast
			have "ang_eq S A H S A H" using equalanglesreflexive[OF `\<not> col S A H`] .
			have "ang_eq F A H F A G" using equalangleshelper[OF `ang_eq F A H F A H` `ray_on A F F` `ray_on A H G`] .
			have "ang_eq S A H S A G" using equalangleshelper[OF `ang_eq S A H S A H` `ray_on A S S` `ray_on A H G`] .
			have "ang_eq F A G F A H" using equalanglessymmetric[OF `ang_eq F A H F A G`] .
			have "ang_eq F A G S A H" using equalanglestransitive[OF `ang_eq F A G F A H` `ang_eq F A H S A H`] .
			have "ang_eq F A G S A G" using equalanglestransitive[OF `ang_eq F A G S A H` `ang_eq S A H S A G`] .
			thus ?thesis by blast
		next
			assume "bet G A H"
			have "bet H A G" using betweennesssymmetryE[OF `bet G A H`] .
			have "ray_on A F F" using `ray_on A F F` .
			have "supplement H A F F G" using supplement_b[OF `ray_on A F F` `bet H A G`] .
			have "supplement H A S S G" using supplement_b[OF `ray_on A S S` `bet H A G`] .
			have "ang_eq F A H S A H" using `ang_eq F A H S A H` .
			have "ang_eq H A F H A S" using equalanglesflip[OF `ang_eq F A H S A H`] .
			have "ang_eq F A G S A G" using supplements[OF `ang_eq H A F H A S` `supplement H A F F G` `supplement H A S S G`] .
			thus ?thesis by blast
		qed
		thus ?thesis by blast
	qed
	have "ang_eq S A G F A G" using equalanglessymmetric[OF `ang_eq F A G S A G`] .
	have "ang_eq F A G D C E" using `ang_eq F A G D C E` .
	have "ang_eq S A G D C E" using equalanglestransitive[OF `ang_eq S A G F A G` `ang_eq F A G D C E`] .
	have "oppo_side Q J T P" using `ang_right J H Q \<and> oppo_side Q J T P` by blast
	have "ray_on H Q S" using `ray_on H Q S` .
	have "ray_on H S Q" using ray5[OF `ray_on H Q S`] .
	have "col J T H" using collinearorder[OF `col H J T`] by blast
	have "oppo_side S J T P" using n9_5[OF `oppo_side Q J T P` `ray_on H S Q` `col J T H`] .
	obtain M where "bet S M P \<and> col J T M \<and> \<not> col J T S" using oppositeside_f[OF `oppo_side S J T P`]  by  blast
	have "bet S M P" using `bet S M P \<and> col J T M \<and> \<not> col J T S` by blast
	have "col J T M" using `bet S M P \<and> col J T M \<and> \<not> col J T S` by blast
	have "\<not> col J T S" using `bet S M P \<and> col J T M \<and> \<not> col J T S` by blast
	have "col A B J" using `col A B J` .
	have "col J T A" using `col J T A` .
	have "col J T B" using `col J T B` .
	have "J \<noteq> T" using `J \<noteq> T` .
	have "col T A B" using collinear4[OF `col J T A` `col J T B` `J \<noteq> T`] .
	have "col A B T" using collinearorder[OF `col T A B`] by blast
	have "col B A T" using collinearorder[OF `col A B T`] by blast
	have "col A J T" using collinear4[OF `col B A J` `col B A T` `B \<noteq> A`] .
	have "col J T A" using collinearorder[OF `col A J T`] by blast
	have "col B J T" using collinear4[OF `col A B J` `col A B T` `A \<noteq> B`] .
	have "col J T B" using collinearorder[OF `col B J T`] by blast
	have "J \<noteq> T" using `J \<noteq> T` .
	have "col A B M" using collinear5[OF `J \<noteq> T` `col J T A` `col J T B` `col J T M`] .
	have "\<not> (col A B S)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col A B S))"
hence "col A B S" by blast
		have "col A B J" using `col A B J` .
		have "col A B T" using `col A B T` .
		have "col J T S" using collinear5[OF `A \<noteq> B` `col A B J` `col A B T` `col A B S`] .
		show "False" using `col J T S` `bet S M P \<and> col J T M \<and> \<not> col J T S` by blast
	qed
	hence "\<not> col A B S" by blast
	have "oppo_side S A B P" using oppositeside_b[OF `bet S M P` `col A B M` `\<not> col A B S`] .
	have "ray_on A B G \<and> ang_eq S A G D C E \<and> oppo_side S A B P" using `ray_on A B G \<and> ang_eq F A G D C E` `ang_eq S A G D C E` `oppo_side S A B P` by blast
	thus ?thesis by blast
qed

end