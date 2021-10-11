theory Prop46
	imports n3_6a n3_7a n8_2 n9_5 Geometry NCdistinct NChelper NCorder PGflip PGsymmetric Prop11B Prop31short Prop34 betweennotequal collinear4 collinearorder collinearparallel collinearright congruenceflip congruencesymmetric congruencetransitive equalanglessymmetric equaltorightisright inequalitysymmetric layoff oppositesidesymmetric parallelNC paralleldef2B parallelsymmetric planeseparation ray2 ray5 rayimpliescollinear samenotopposite triangletoparallelogram
begin

theorem(in euclidean_geometry) Prop46:
	assumes 
		"A \<noteq> B"
		"\<not> col A B R"
	shows "\<exists> D E. square A B E D \<and> oppo_side D A B R \<and> parallelogram A B E D"
proof -
	have "B \<noteq> A" using inequalitysymmetric[OF `A \<noteq> B`] .
	obtain F where "bet B A F \<and> seg_eq A F A B" using extensionE[OF `B \<noteq> A` `A \<noteq> B`]  by  blast
	have "bet B A F" using `bet B A F \<and> seg_eq A F A B` by blast
	have "\<not> col B A R" using NCorder[OF `\<not> col A B R`] by blast
	have "col B A F" using collinear_b `bet B A F \<and> seg_eq A F A B` by blast
	have "B = B" using equalityreflexiveE.
	have "col B A B" using collinear_b `B = B` by blast
	have "B \<noteq> F" using betweennotequal[OF `bet B A F`] by blast
	have "\<not> col B F R" using NChelper[OF `\<not> col B A R` `col B A B` `col B A F` `B \<noteq> F`] .
	obtain C where "ang_right B A C \<and> oppo_side C B F R" using Prop11B[OF `bet B A F` `\<not> col B F R`]  by  blast
	have "oppo_side C B F R" using `ang_right B A C \<and> oppo_side C B F R` by blast
	have "\<not> col B F C" using oppositeside_f[OF `oppo_side C B F R`] by blast
	have "col B F A" using collinearorder[OF `col B A F`] by blast
	have "col B F B" using collinear_b `B = B` by blast
	have "\<not> col B A C" using NChelper[OF `\<not> col B F C` `col B F B` `col B F A` `B \<noteq> A`] .
	have "A \<noteq> C" using NCdistinct[OF `\<not> col B A C`] by blast
	obtain D where "ray_on A C D \<and> seg_eq A D A B" using layoff[OF `A \<noteq> C` `A \<noteq> B`]  by  blast
	have "ray_on A C D" using `ray_on A C D \<and> seg_eq A D A B` by blast
	have "ray_on A D C" using ray5[OF `ray_on A C D`] .
	have "A = A" using equalityreflexiveE.
	have "col A B A" using collinear_b `A = A` by blast
	obtain q where "bet C q R \<and> col B F q \<and> \<not> col B F C" using oppositeside_f[OF `oppo_side C B F R`]  by  blast
	have "bet C q R" using `bet C q R \<and> col B F q \<and> \<not> col B F C` by blast
	have "col B F q" using `bet C q R \<and> col B F q \<and> \<not> col B F C` by blast
	have "\<not> col B F C" using `\<not> col B F C` .
	have "col B F A" using `col B F A` .
	have "col F B q" using collinearorder[OF `col B F q`] by blast
	have "B = B" using equalityreflexiveE.
	have "\<not> col A B C" using NChelper[OF `\<not> col B F C` `col B F A` `col B F B` `A \<noteq> B`] .
	have "col A B F" using collinearorder[OF `col B A F`] by blast
	have "col F B A" using collinearorder[OF `col A B F`] by blast
	have "B \<noteq> F" using betweennotequal[OF `bet B A F`] by blast
	have "F \<noteq> B" using inequalitysymmetric[OF `B \<noteq> F`] .
	have "col B A q" using collinear4[OF `col F B A` `col F B q` `F \<noteq> B`] .
	have "col A B q" using collinearorder[OF `col B A q`] by blast
	have "oppo_side C A B R" using oppositeside_b[OF `bet C q R` `col A B q` `\<not> col A B C`] .
	have "oppo_side D A B R" using n9_5[OF `oppo_side C A B R` `ray_on A D C` `col A B A`] .
	have "\<not> col C A B" using NCorder[OF `\<not> col A B C`] by blast
	have "A = A" using equalityreflexiveE.
	have "col C A A" using collinear_b `A = A` by blast
	have "col A C D" using rayimpliescollinear[OF `ray_on A C D`] .
	have "col C A D" using collinearorder[OF `col A C D`] by blast
	have "A \<noteq> D" using ray2[OF `ray_on A D C`] .
	have "\<not> col C A B" using NCorder[OF `\<not> col A B C`] by blast
	have "\<not> col C A B \<and> col C A A \<and> col C A D \<and> A \<noteq> D" using `\<not> col C A B` `col C A A` `col C A D` `A \<noteq> D` by blast
	have "\<not> col A D B" using NChelper[OF `\<not> col C A B` `col C A A` `col C A D` `A \<noteq> D`] .
	have "\<not> col A B D" using NCorder[OF `\<not> col A D B`] by blast
	have "bet F A B" using betweennesssymmetryE[OF `bet B A F`] .
	have "col A B F" using `col A B F` .
	have "col A B B" using collinear_b `B = B` by blast
	have "A \<noteq> B" using `A \<noteq> B` .
	have "\<not> col F B D" using NChelper[OF `\<not> col A B D` `col A B F` `col A B B` `F \<noteq> B`] .
	obtain G M e where "bet G D e \<and> ang_eq G D A D A B \<and> parallel G e F B \<and> bet G M B \<and> bet D M A" using Prop31short[OF `bet F A B` `\<not> col F B D`]  by  blast
	have "bet G D e" using `bet G D e \<and> ang_eq G D A D A B \<and> parallel G e F B \<and> bet G M B \<and> bet D M A` by blast
	have "parallel G e F B" using `bet G D e \<and> ang_eq G D A D A B \<and> parallel G e F B \<and> bet G M B \<and> bet D M A` by blast
	have "bet G M B" using `bet G D e \<and> ang_eq G D A D A B \<and> parallel G e F B \<and> bet G M B \<and> bet D M A` by blast
	have "bet D M A" using `bet G D e \<and> ang_eq G D A D A B \<and> parallel G e F B \<and> bet G M B \<and> bet D M A` by blast
	have "parallel G e A B" using collinearparallel[OF `parallel G e F B` `col F B A` `A \<noteq> B`] .
	have "parallel A B G e" using parallelsymmetric[OF `parallel G e A B`] .
	have "col G D e" using collinear_b `bet G D e \<and> ang_eq G D A D A B \<and> parallel G e F B \<and> bet G M B \<and> bet D M A` by blast
	have "col G e D" using collinearorder[OF `col G D e`] by blast
	obtain E where "parallelogram D E B A \<and> col G e E" using triangletoparallelogram[OF `parallel A B G e` `col G e D`]  by  blast
	have "col G e E" using `parallelogram D E B A \<and> col G e E` by blast
	have "ang_right B A C" using `ang_right B A C \<and> oppo_side C B F R` by blast
	have "ang_right C A B" using n8_2[OF `ang_right B A C`] .
	have "col C A D" using `col C A D` .
	have "D \<noteq> A" using inequalitysymmetric[OF `A \<noteq> D`] .
	have "ang_right D A B" using collinearright[OF `ang_right C A B` `col C A D` `D \<noteq> A`] .
	have "ang_right B A D" using n8_2[OF `ang_right D A B`] .
	have "ang_eq G D A D A B" using `bet G D e \<and> ang_eq G D A D A B \<and> parallel G e F B \<and> bet G M B \<and> bet D M A` by blast
	have "ang_right G D A" using equaltorightisright[OF `ang_right D A B` `ang_eq G D A D A B`] .
	obtain p where "bet G D p \<and> seg_eq G D p D \<and> seg_eq G A p A \<and> D \<noteq> A" using rightangle_f[OF `ang_right G D A`]  by  blast
	have "bet G D p" using `bet G D p \<and> seg_eq G D p D \<and> seg_eq G A p A \<and> D \<noteq> A` by blast
	have "seg_eq G D p D" using `bet G D p \<and> seg_eq G D p D \<and> seg_eq G A p A \<and> D \<noteq> A` by blast
	have "seg_eq G A p A" using `bet G D p \<and> seg_eq G D p D \<and> seg_eq G A p A \<and> D \<noteq> A` by blast
	have "D \<noteq> A" using `D \<noteq> A` .
	have "bet p D G" using betweennesssymmetryE[OF `bet G D p`] .
	have "seg_eq p D G D" using congruencesymmetric[OF `seg_eq G D p D`] .
	have "seg_eq p A G A" using congruencesymmetric[OF `seg_eq G A p A`] .
	have "ang_right p D A" using rightangle_b[OF `bet p D G` `seg_eq p D G D` `seg_eq p A G A` `D \<noteq> A`] .
	have "parallelogram D E B A" using `parallelogram D E B A \<and> col G e E` by blast
	have "parallel D A E B" using parallelogram_f[OF `parallelogram D E B A`] by blast
	have "tarski_parallel D A E B" using paralleldef2B[OF `parallel D A E B`] .
	have "same_side E B D A" using tarski_parallel_f[OF `tarski_parallel D A E B`] by blast
	have "D = D" using equalityreflexiveE.
	have "col D A D" using collinear_b `D = D` by blast
	have "\<not> col D A B" using NCorder[OF `\<not> col A B D`] by blast
	have "bet B M G" using betweennesssymmetryE[OF `bet G M B`] .
	have "col D M A" using collinear_b `bet G D e \<and> ang_eq G D A D A B \<and> parallel G e F B \<and> bet G M B \<and> bet D M A` by blast
	have "col D A M" using collinearorder[OF `col D M A`] by blast
	have "oppo_side B D A G" using oppositeside_b[OF `bet B M G` `col D A M` `\<not> col D A B`] .
	have "oppo_side E D A G" using planeseparation[OF `same_side E B D A` `oppo_side B D A G`] .
	have "\<not> col D A E" using oppositeside_f[OF `oppo_side E D A G`] by blast
	have "oppo_side G D A E" using oppositesidesymmetric[OF `oppo_side E D A G`] .
	have "\<not> col D A G" using oppositeside_f[OF `oppo_side G D A E`] by blast
	obtain d where "bet E d G \<and> col D A d \<and> \<not> col D A E" using oppositeside_f[OF `oppo_side E D A G`]  by  blast
	have "bet E d G" using `bet E d G \<and> col D A d \<and> \<not> col D A E` by blast
	have "col D A d" using `bet E d G \<and> col D A d \<and> \<not> col D A E` by blast
	have "\<not> col D A E" using `\<not> col D A E` .
	have "E \<noteq> G" using betweennotequal[OF `bet E d G`] by blast
	have "G \<noteq> E" using inequalitysymmetric[OF `E \<noteq> G`] .
	have "G \<noteq> D" using NCdistinct[OF `\<not> col D A G`] by blast
	have "D \<noteq> E" using NCdistinct[OF `\<not> col D A E`] by blast
	have "\<not> (same_side E G D A)"
	proof (rule ccontr)
		assume "\<not> (\<not> (same_side E G D A))"
hence "same_side E G D A" by blast
		have "\<not> (oppo_side E D A G)" using samenotopposite[OF `same_side E G D A`] .
		show "False" using `\<not> (oppo_side E D A G)` `oppo_side E D A G` by blast
	qed
	hence "\<not> (same_side E G D A)" by blast
	have "\<not> (bet D G E)"
	proof (rule ccontr)
		assume "\<not> (\<not> (bet D G E))"
hence "bet D G E" by blast
		have "col D A D" using `col D A D` .
		have "bet G D e" using `bet G D e` .
		have "bet E G D" using betweennesssymmetryE[OF `bet D G E`] .
		have "bet E D e" using n3_7a[OF `bet E G D` `bet G D e`] .
		have "same_side E G D A" using sameside_b[OF `col D A D` `col D A D` `bet E D e` `bet G D e` `\<not> col D A E` `\<not> col D A G`] .
		show "False" using `same_side E G D A` `\<not> (same_side E G D A)` by blast
	qed
	hence "\<not> (bet D G E)" by blast
	have "\<not> (bet G E D)"
	proof (rule ccontr)
		assume "\<not> (\<not> (bet G E D))"
hence "bet G E D" by blast
		have "bet G D e" using `bet G D e` .
		have "bet E D e" using n3_6a[OF `bet G E D` `bet G D e`] .
		have "same_side E G D A" using sameside_b[OF `col D A D` `col D A D` `bet E D e` `bet G D e` `\<not> col D A E` `\<not> col D A G`] .
		show "False" using `same_side E G D A` `\<not> (same_side E G D A)` by blast
	qed
	hence "\<not> (bet G E D)" by blast
	have "col e G D" using collinearorder[OF `col G D e`] by blast
	have "col e G E" using collinearorder[OF `col G e E`] by blast
	have "\<not> col G e F" using parallelNC[OF `parallel G e F B`] by blast
	have "G \<noteq> e" using NCdistinct[OF `\<not> col G e F`] by blast
	have "e \<noteq> G" using inequalitysymmetric[OF `G \<noteq> e`] .
	have "col G D E" using collinear4[OF `col e G D` `col e G E` `e \<noteq> G`] .
	have "G = D \<or> G = E \<or> D = E \<or> bet D G E \<or> bet G D E \<or> bet G E D" using collinear_f[OF `col G D E`] .
	consider "G = D"|"G = E"|"D = E"|"bet D G E"|"bet G D E"|"bet G E D" using `G = D \<or> G = E \<or> D = E \<or> bet D G E \<or> bet G D E \<or> bet G E D`  by blast
	hence "bet G D E"
	proof (cases)
		assume "G = D"
		have "\<not> (\<not> (bet G D E))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (bet G D E)))"
hence "\<not> (bet G D E)" by blast
			have "G \<noteq> D" using `G \<noteq> D` .
			show "False" using `G \<noteq> D` `G = D` by blast
		qed
		hence "bet G D E" by blast
		thus ?thesis by blast
	next
		assume "G = E"
		have "\<not> (\<not> (bet G D E))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (bet G D E)))"
hence "\<not> (bet G D E)" by blast
			have "G \<noteq> E" using `G \<noteq> E` .
			show "False" using `G \<noteq> E` `G = E` by blast
		qed
		hence "bet G D E" by blast
		thus ?thesis by blast
	next
		assume "D = E"
		have "\<not> (\<not> (bet G D E))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (bet G D E)))"
hence "\<not> (bet G D E)" by blast
			have "D \<noteq> E" using `D \<noteq> E` .
			show "False" using `D \<noteq> E` `D = E` by blast
		qed
		hence "bet G D E" by blast
		thus ?thesis by blast
	next
		assume "bet D G E"
		have "\<not> (\<not> (bet G D E))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (bet G D E)))"
hence "\<not> (bet G D E)" by blast
			have "\<not> (bet D G E)" using `\<not> (bet D G E)` .
			show "False" using `\<not> (bet D G E)` `bet D G E` by blast
		qed
		hence "bet G D E" by blast
		thus ?thesis by blast
	next
		assume "bet G D E"
		thus ?thesis by blast
	next
		assume "bet G E D"
		have "\<not> (\<not> (bet G D E))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (bet G D E)))"
hence "\<not> (bet G D E)" by blast
			have "\<not> (bet G E D)" using `\<not> (bet G E D)` .
			show "False" using `\<not> (bet G E D)` `bet G E D` by blast
		qed
		hence "bet G D E" by blast
		thus ?thesis by blast
	qed
	have "col G D E" using collinear_b[OF `G = D \<or> G = E \<or> D = E \<or> bet D G E \<or> bet G D E \<or> bet G E D`] .
	have "E \<noteq> D" using inequalitysymmetric[OF `D \<noteq> E`] .
	have "ang_right E D A" using collinearright[OF `ang_right G D A` `col G D E` `E \<noteq> D`] .
	have "parallelogram D E B A" using `parallelogram D E B A` .
	have "seg_eq D A E B \<and> seg_eq D E A B \<and> ang_eq E D A A B E \<and> ang_eq D A B B E D \<and> tri_cong E D A A B E" using Prop34[OF `parallelogram D E B A`] .
	have "seg_eq D A E B" using `seg_eq D A E B \<and> seg_eq D E A B \<and> ang_eq E D A A B E \<and> ang_eq D A B B E D \<and> tri_cong E D A A B E` by blast
	have "seg_eq D E A B" using `seg_eq D A E B \<and> seg_eq D E A B \<and> ang_eq E D A A B E \<and> ang_eq D A B B E D \<and> tri_cong E D A A B E` by blast
	have "ang_eq E D A A B E" using `seg_eq D A E B \<and> seg_eq D E A B \<and> ang_eq E D A A B E \<and> ang_eq D A B B E D \<and> tri_cong E D A A B E` by blast
	have "ang_eq D A B B E D" using `seg_eq D A E B \<and> seg_eq D E A B \<and> ang_eq E D A A B E \<and> ang_eq D A B B E D \<and> tri_cong E D A A B E` by blast
	have "seg_eq A B D E" using congruencesymmetric[OF `seg_eq D E A B`] .
	have "seg_eq A B E D" using congruenceflip[OF `seg_eq A B D E`] by blast
	have "seg_eq A D A B" using `ray_on A C D \<and> seg_eq A D A B` by blast
	have "seg_eq A B A D" using congruencesymmetric[OF `seg_eq A D A B`] .
	have "seg_eq A D E B" using congruenceflip[OF `seg_eq D A E B`] by blast
	have "seg_eq A B E B" using congruencetransitive[OF `seg_eq A B A D` `seg_eq A D E B`] .
	have "seg_eq A B B E" using congruenceflip[OF `seg_eq A B E B`] by blast
	have "seg_eq A B D A" using congruenceflip[OF `seg_eq A B A D`] by blast
	have "ang_right D A B" using `ang_right D A B` .
	have "ang_right E D A" using `ang_right E D A` .
	have "ang_eq B E D D A B" using equalanglessymmetric[OF `ang_eq D A B B E D`] .
	have "ang_eq A B E E D A" using equalanglessymmetric[OF `ang_eq E D A A B E`] .
	have "ang_right B E D" using equaltorightisright[OF `ang_right D A B` `ang_eq B E D D A B`] .
	have "ang_right A B E" using equaltorightisright[OF `ang_right E D A` `ang_eq A B E E D A`] .
	have "seg_eq A B E D \<and> seg_eq A B B E \<and> seg_eq A B D A \<and> ang_right D A B \<and> ang_right A B E \<and> ang_right B E D \<and> ang_right E D A" using `seg_eq A B E D` `seg_eq A B B E` `seg_eq A B D A` `ang_right D A B` `ang_right A B E` `ang_right B E D` `ang_right E D A` by blast
	have "square A B E D" using square_b[OF `seg_eq A B E D` `seg_eq A B B E` `seg_eq A B D A` `ang_right D A B` `ang_right A B E` `ang_right B E D` `ang_right E D A`] .
	have "parallelogram B A D E" using PGsymmetric[OF `parallelogram D E B A`] .
	have "parallelogram A B E D" using PGflip[OF `parallelogram B A D E`] .
	have "square A B E D \<and> oppo_side D A B R \<and> parallelogram A B E D" using `square A B E D` `oppo_side D A B R` `parallelogram A B E D` by blast
	thus ?thesis by blast
qed

end