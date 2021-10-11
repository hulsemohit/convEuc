theory Prop27
	imports n3_7b ABCequalsCBA Geometry Prop16 angledistinct angleorderrespectscongruence angleorderrespectscongruence2 angletrichotomy betweennotequal collinear4 collinear5 collinearbetween collinearorder equalanglesflip equalangleshelper equalanglesreflexive equalanglessymmetric equalanglestransitive inequalitysymmetric planeseparation ray1 ray4 ray5 samesidesymmetric supplements
begin

theorem(in euclidean_geometry) Prop27:
	assumes 
		"bet A E B"
		"bet C F D"
		"ang_eq A E F E F D"
		"oppo_side A E F D"
	shows "parallel A B C D"
proof -
	have "A \<noteq> B" using betweennotequal[OF `bet A E B`] by blast
	have "C \<noteq> D" using betweennotequal[OF `bet C F D`] by blast
	obtain H where "bet A H D \<and> col E F H \<and> \<not> col E F A" using oppositeside_f[OF `oppo_side A E F D`]  by  blast
	have "bet A H D" using `bet A H D \<and> col E F H \<and> \<not> col E F A` by blast
	have "col E F H" using `bet A H D \<and> col E F H \<and> \<not> col E F A` by blast
	have "\<not> col E F A" using `bet A H D \<and> col E F H \<and> \<not> col E F A` by blast
	have "col A E B" using collinear_b `bet A E B` by blast
	have "A \<noteq> E" using betweennotequal[OF `bet A E B`] by blast
	have "col C F D" using collinear_b `bet C F D` by blast
	have "F \<noteq> D" using betweennotequal[OF `bet C F D`] by blast
	have "ang_eq E F D A E F" using equalanglessymmetric[OF `ang_eq A E F E F D`] .
	have "\<not> col E F D" using equalangles_f[OF `ang_eq E F D A E F`] by blast
	have "E \<noteq> F" using angledistinct[OF `ang_eq A E F E F D`] by blast
	have "F \<noteq> E" using inequalitysymmetric[OF `E \<noteq> F`] .
	have "\<not> (meets A B C D)"
	proof (rule ccontr)
		assume "\<not> (\<not> (meets A B C D))"
hence "meets A B C D" by blast
		obtain G where "A \<noteq> B \<and> C \<noteq> D \<and> col A B G \<and> col C D G" using meet_f[OF `meets A B C D`]  by  blast
		have "col A B G" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B G \<and> col C D G` by blast
		have "col C D G" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B G \<and> col C D G` by blast
		have "col B A G" using collinearorder[OF `col A B G`] by blast
		have "col B A E" using collinearorder[OF `col A E B`] by blast
		have "B \<noteq> A" using inequalitysymmetric[OF `A \<noteq> B`] .
		have "col A G E" using collinear4[OF `col B A G` `col B A E` `B \<noteq> A`] .
		have "col A E G" using collinearorder[OF `col A G E`] by blast
		have "F = F" using equalityreflexiveE.
		have "ray_on E F F" using ray4 `F = F` `E \<noteq> F` by blast
		have "supplement A E F F B" using supplement_b[OF `ray_on E F F` `bet A E B`] .
		have "E = E" using equalityreflexiveE.
		have "ray_on F E E" using ray4 `E = E` `F \<noteq> E` by blast
		have "bet D F C" using betweennesssymmetryE[OF `bet C F D`] .
		have "supplement D F E E C" using supplement_b[OF `ray_on F E E` `bet D F C`] .
		have "ang_eq E F D D F E" using ABCequalsCBA[OF `\<not> col E F D`] .
		have "ang_eq A E F D F E" using equalanglestransitive[OF `ang_eq A E F E F D` `ang_eq E F D D F E`] .
		have "ang_eq F E B E F C" using supplements[OF `ang_eq A E F D F E` `supplement A E F F B` `supplement D F E E C`] .
		have "ang_eq B E F C F E" using equalanglesflip[OF `ang_eq F E B E F C`] .
		have "\<not> (bet A E G)"
		proof (rule ccontr)
			assume "\<not> (\<not> (bet A E G))"
hence "bet A E G" by blast
			have "E = E" using equalityreflexiveE.
			have "col E F E" using collinear_b `E = E` by blast
			have "bet G E A" using betweennesssymmetryE[OF `bet A E G`] .
			have "\<not> col E F D" using `\<not> col E F D` .
			have "col C D G" using `col C D G` .
			have "col C F D" using collinear_b `bet C F D` by blast
			have "col C D F" using collinearorder[OF `col C F D`] by blast
			have "C \<noteq> D" using betweennotequal[OF `bet C F D`] by blast
			have "col D G F" using collinear4[OF `col C D G` `col C D F` `C \<noteq> D`] .
			have "col G F D" using collinearorder[OF `col D G F`] by blast
			have "\<not> (F = G)"
			proof (rule ccontr)
				assume "\<not> (F \<noteq> G)"
				hence "F = G" by blast
				have "col A E F" using `col A E G` `F = G` by blast
				have "col E F A" using collinearorder[OF `col A E F`] by blast
				show "False" using `col E F A` `bet A H D \<and> col E F H \<and> \<not> col E F A` by blast
			qed
			hence "F \<noteq> G" by blast
			have "G \<noteq> F" using inequalitysymmetric[OF `F \<noteq> G`] .
			have "\<not> (col E F G)"
			proof (rule ccontr)
				assume "\<not> (\<not> (col E F G))"
hence "col E F G" by blast
				have "col G F E" using collinearorder[OF `col E F G`] by blast
				have "col F E D" using collinear4[OF `col G F E` `col G F D` `G \<noteq> F`] .
				have "col E F D" using collinearorder[OF `col F E D`] by blast
				have "\<not> col E F D" using `\<not> col E F D` .
				show "False" using `\<not> col E F D` `col E F D` by blast
			qed
			hence "\<not> col E F G" by blast
			have "bet D H A" using betweennesssymmetryE[OF `bet A H D`] .
			have "col E F H" using `col E F H` .
			have "same_side D G E F" using sameside_b[OF `col E F H` `col E F E` `bet D H A` `bet G E A` `\<not> col E F D` `\<not> col E F G`] .
			have "same_side G D E F" using samesidesymmetric[OF `same_side D G E F`] by blast
			have "F = F" using equalityreflexiveE.
			have "col E F F" using collinear_b `F = F` by blast
			have "\<not> col E F D" using `\<not> col E F D` .
			have "bet D F C" using betweennesssymmetryE[OF `bet C F D`] .
			have "oppo_side D E F C" using oppositeside_b[OF `bet D F C` `col E F F` `\<not> col E F D`] .
			have "oppo_side G E F C" using planeseparation[OF `same_side G D E F` `oppo_side D E F C`] .
			obtain R where "bet G R C \<and> col E F R \<and> \<not> col E F G" using oppositeside_f[OF `oppo_side G E F C`]  by  blast
			have "bet G R C" using `bet G R C \<and> col E F R \<and> \<not> col E F G` by blast
			have "\<not> (F \<noteq> R)"
			proof (rule ccontr)
				assume "\<not> (\<not> (F \<noteq> R))"
hence "F \<noteq> R" by blast
				have "col G R C" using collinear_b `bet G R C \<and> col E F R \<and> \<not> col E F G` by blast
				have "col C D G" using `col C D G` .
				have "col C G D" using collinearorder[OF `col C D G`] by blast
				have "col C G R" using collinearorder[OF `col G R C`] by blast
				have "G \<noteq> C" using betweennotequal[OF `bet G R C`] by blast
				have "C \<noteq> G" using inequalitysymmetric[OF `G \<noteq> C`] .
				have "col G C R" using collinearorder[OF `col C G R`] by blast
				have "col G C D" using collinearorder[OF `col C D G`] by blast
				have "G \<noteq> C" using inequalitysymmetric[OF `C \<noteq> G`] .
				have "col E F R" using `bet G R C \<and> col E F R \<and> \<not> col E F G` by blast
				have "R \<noteq> F" using inequalitysymmetric[OF `F \<noteq> R`] .
				have "col C G R" using collinearorder[OF `col G C R`] by blast
				have "col C D F" using collinearorder[OF `col C F D`] by blast
				have "col C D G" using `col C D G` .
				have "col D F G" using collinear4[OF `col C D F` `col C D G` `C \<noteq> D`] .
				have "col D F C" using collinearorder[OF `col C D F`] by blast
				have "F \<noteq> D" using betweennotequal[OF `bet C F D`] by blast
				have "D \<noteq> F" using inequalitysymmetric[OF `F \<noteq> D`] .
				have "col F G C" using collinear4[OF `col D F G` `col D F C` `D \<noteq> F`] .
				have "col C G F" using collinearorder[OF `col F G C`] by blast
				have "col C G D" using collinearorder[OF `col C D G`] by blast
				have "col R F D" using collinear5[OF `C \<noteq> G` `col C G R` `col C G F` `col C G D`] .
				have "col R F E" using collinearorder[OF `col E F R`] by blast
				have "col F D E" using collinear4[OF `col R F D` `col R F E` `R \<noteq> F`] .
				have "col E F D" using collinearorder[OF `col F D E`] by blast
				have "\<not> col E F D" using `\<not> col E F D` .
				show "False" using `\<not> col E F D` `col E F D` by blast
			qed
			hence "F = R" by blast
			have "bet G F C" using `bet G R C` `F = R` by blast
			have "\<not> (col E G F)"
			proof (rule ccontr)
				assume "\<not> (\<not> (col E G F))"
hence "col E G F" by blast
				have "col E F G" using collinearorder[OF `col E G F`] by blast
				have "\<not> col E F G" using `\<not> col E F G` .
				show "False" using `\<not> col E F G` `col E F G` by blast
			qed
			hence "\<not> col E G F" by blast
			have "triangle E G F" using triangle_b[OF `\<not> col E G F`] .
			have "ang_lt G E F E F C" using Prop16[OF `triangle E G F` `bet G F C`] by blast
			have "ang_eq F E B E F C" using `ang_eq F E B E F C` .
			have "ang_lt G E F F E B" using angleorderrespectscongruence[OF `ang_lt G E F E F C` `ang_eq F E B E F C`] .
			have "F = F" using equalityreflexiveE.
			have "ray_on E F F" using ray4 `F = F` `E \<noteq> F` by blast
			have "ray_on E G B" using ray_b[OF `bet A E B` `bet A E G`] .
			have "\<not> (col G E F)"
			proof (rule ccontr)
				assume "\<not> (\<not> (col G E F))"
hence "col G E F" by blast
				have "col E G F" using collinearorder[OF `col G E F`] by blast
				show "False" using `col E G F` `\<not> col E G F` by blast
			qed
			hence "\<not> col G E F" by blast
			have "ang_eq G E F G E F" using equalanglesreflexive[OF `\<not> col G E F`] .
			have "ang_eq G E F B E F" using equalangleshelper[OF `ang_eq G E F G E F` `ray_on E G B` `ray_on E F F`] .
			have "\<not> col B E F" using equalangles_f[OF `ang_eq B E F C F E`] by blast
			have "ang_eq B E F F E B" using ABCequalsCBA[OF `\<not> col B E F`] .
			have "ang_eq G E F F E B" using equalanglestransitive[OF `ang_eq G E F B E F` `ang_eq B E F F E B`] .
			have "ang_eq F E B G E F" using equalanglessymmetric[OF `ang_eq G E F F E B`] .
			have "ang_lt F E B F E B" using angleorderrespectscongruence2[OF `ang_lt G E F F E B` `ang_eq F E B G E F`] .
			have "\<not> (ang_lt F E B F E B)" using angletrichotomy[OF `ang_lt F E B F E B`] .
			show "False" using `\<not> (ang_lt F E B F E B)` `ang_lt F E B F E B` by blast
		qed
		hence "\<not> (bet A E G)" by blast
		have "\<not> (ray_on E A G)"
		proof (rule ccontr)
			assume "\<not> (\<not> (ray_on E A G))"
hence "ray_on E A G" by blast
			have "F = F" using equalityreflexiveE.
			have "ray_on E F F" using ray4 `F = F` `E \<noteq> F` by blast
			have "ray_on E G A" using ray5[OF `ray_on E A G`] .
			have "ang_eq E F D A E F" using equalanglessymmetric[OF `ang_eq A E F E F D`] .
			have "ang_eq E F D G E F" using equalangleshelper[OF `ang_eq E F D A E F` `ray_on E A G` `ray_on E F F`] .
			have "bet B E A" using betweennesssymmetryE[OF `bet A E B`] .
			have "bet E A G \<or> G = A \<or> bet E G A" using ray1[OF `ray_on E G A`] .
			consider "bet E A G"|"G = A"|"bet E G A" using `bet E A G \<or> G = A \<or> bet E G A`  by blast
			hence "bet B E G"
			proof (cases)
				assume "bet E A G"
				have "bet B E A" using `bet B E A` .
				have "bet B E G" using n3_7b[OF `bet B E A` `bet E A G`] .
				thus ?thesis by blast
			next
				assume "G = A"
				have "bet B E G" using `bet B E A` `G = A` by blast
				thus ?thesis by blast
			next
				assume "bet E G A"
				have "bet B E G" using innertransitivityE[OF `bet B E A` `bet E G A`] .
				thus ?thesis by blast
			qed
			have "bet G E B" using betweennesssymmetryE[OF `bet B E G`] .
			have "E = E" using equalityreflexiveE.
			have "col E F E" using collinear_b `E = E` by blast
			have "\<not> (col E F G)"
			proof (rule ccontr)
				assume "\<not> (\<not> (col E F G))"
hence "col E F G" by blast
				have "col A B G" using `col A B G` .
				have "col B A G" using collinearorder[OF `col A B G`] by blast
				have "col A E B" using collinear_b `bet A E B` by blast
				have "col B A E" using collinearorder[OF `col A E B`] by blast
				have "col A G E" using collinear4[OF `col B A G` `col B A E` `B \<noteq> A`] .
				have "col G E A" using collinearorder[OF `col A E G`] by blast
				have "col G E F" using collinearorder[OF `col E F G`] by blast
				have "E \<noteq> G" using betweennotequal[OF `bet B E G`] by blast
				have "G \<noteq> E" using inequalitysymmetric[OF `E \<noteq> G`] .
				have "col E A F" using collinear4[OF `col G E A` `col G E F` `G \<noteq> E`] .
				have "col E F A" using collinearorder[OF `col E A F`] by blast
				have "\<not> col E F A" using `\<not> col E F A` .
				show "False" using `\<not> col E F A` `col E F A` by blast
			qed
			hence "\<not> col E F G" by blast
			have "\<not> col E F A" using `\<not> col E F A` .
			have "same_side A G E F" using sameside_b[OF `col E F E` `col E F E` `bet A E B` `bet G E B` `\<not> col E F A` `\<not> col E F G`] .
			have "same_side G A E F" using samesidesymmetric[OF `same_side A G E F`] by blast
			have "oppo_side A E F D" using `oppo_side A E F D` .
			have "oppo_side G E F D" using planeseparation[OF `same_side G A E F` `oppo_side A E F D`] .
			obtain P where "bet G P D \<and> col E F P \<and> \<not> col E F G" using oppositeside_f[OF `oppo_side G E F D`]  by  blast
			have "bet G P D" using `bet G P D \<and> col E F P \<and> \<not> col E F G` by blast
			have "col G P D" using collinear_b `bet G P D \<and> col E F P \<and> \<not> col E F G` by blast
			have "col E F P" using `bet G P D \<and> col E F P \<and> \<not> col E F G` by blast
			have "\<not> (P \<noteq> F)"
			proof (rule ccontr)
				assume "\<not> (\<not> (P \<noteq> F))"
hence "P \<noteq> F" by blast
				have "G \<noteq> D" using betweennotequal[OF `bet G P D`] by blast
				have "col G D P" using collinearorder[OF `col G P D`] by blast
				have "col C D G" using `col C D G` .
				have "col C F D" using collinear_b `bet C F D` by blast
				have "col C D F" using collinearorder[OF `col C F D`] by blast
				have "col D G F" using collinear4[OF `col C D G` `col C D F` `C \<noteq> D`] .
				have "col G D F" using collinearorder[OF `col D G F`] by blast
				have "col D P F" using collinear4[OF `col G D P` `col G D F` `G \<noteq> D`] .
				have "col P F D" using collinearorder[OF `col D P F`] by blast
				have "col P F E" using collinearorder[OF `col E F P`] by blast
				have "col F D E" using collinear4[OF `col P F D` `col P F E` `P \<noteq> F`] .
				have "\<not> (col F D E)"
				proof (rule ccontr)
					assume "\<not> (\<not> (col F D E))"
hence "col F D E" by blast
					have "col E F D" using collinearorder[OF `col F D E`] by blast
					show "False" using `col E F D` `\<not> col E F D` by blast
				qed
				hence "\<not> col F D E" by blast
				show "False" using `\<not> col F D E` `col F D E` by blast
			qed
			hence "P = F" by blast
			have "bet G F D" using `bet G P D` `P = F` by blast
			have "ray_on E A G" using `ray_on E A G` .
			have "\<not> (col F E A)"
			proof (rule ccontr)
				assume "\<not> (\<not> (col F E A))"
hence "col F E A" by blast
				have "col E F A" using collinearorder[OF `col F E A`] by blast
				show "False" using `col E F A` `bet A H D \<and> col E F H \<and> \<not> col E F A` by blast
			qed
			hence "\<not> col F E A" by blast
			have "ang_eq F E A F E A" using equalanglesreflexive[OF `\<not> col F E A`] .
			have "ang_eq F E A F E G" using equalangleshelper[OF `ang_eq F E A F E A` `ray_on E F F` `ray_on E A G`] .
			have "ang_eq F E G F E A" using equalanglessymmetric[OF `ang_eq F E A F E G`] .
			have "\<not> col F E G" using equalangles_f[OF `ang_eq F E G F E A`] by blast
			have "bet G F D" using `bet G F D` .
			have "\<not> (col E G F)"
			proof (rule ccontr)
				assume "\<not> (\<not> (col E G F))"
hence "col E G F" by blast
				have "col F E G" using collinearorder[OF `col E G F`] by blast
				show "False" using `col F E G` `\<not> col F E G` by blast
			qed
			hence "\<not> col E G F" by blast
			have "triangle E G F" using triangle_b[OF `\<not> col E G F`] .
			have "ang_lt G E F E F D" using Prop16[OF `triangle E G F` `bet G F D`] by blast
			have "ang_lt E F D E F D" using angleorderrespectscongruence2[OF `ang_lt G E F E F D` `ang_eq E F D G E F`] .
			have "\<not> (ang_lt E F D E F D)" using angletrichotomy[OF `ang_lt E F D E F D`] .
			show "False" using `\<not> (ang_lt E F D E F D)` `ang_lt E F D E F D` by blast
		qed
		hence "\<not> (ray_on E A G)" by blast
		have "A = E \<or> A = G \<or> E = G \<or> bet E A G \<or> bet A E G \<or> bet A G E" using collinear_f[OF `col A E G`] .
		consider "A = E"|"A = G"|"E = G"|"bet E A G"|"bet A E G"|"bet A G E" using `A = E \<or> A = G \<or> E = G \<or> bet E A G \<or> bet A E G \<or> bet A G E`  by blast
		hence "\<not> (meets A B C D)"
		proof (cases)
			assume "A = E"
			have "\<not> (meets A B C D)"
			proof (rule ccontr)
				assume "\<not> (\<not> (meets A B C D))"
hence "meets A B C D" by blast
				have "A \<noteq> E" using `A \<noteq> E` .
				show "False" using `A \<noteq> E` `A = E` by blast
			qed
			hence "\<not> (meets A B C D)" by blast
			thus ?thesis by blast
		next
			assume "A = G"
			have "\<not> (H \<noteq> F)"
			proof (rule ccontr)
				assume "\<not> (\<not> (H \<noteq> F))"
hence "H \<noteq> F" by blast
				have "col C D G" using `col C D G` .
				have "col C D F" using collinearorder[OF `col C F D`] by blast
				have "C \<noteq> D" using `C \<noteq> D` .
				have "col D G F" using collinear4[OF `col C D G` `col C D F` `C \<noteq> D`] .
				have "col D A F" using `col D G F` `A = G` by blast
				have "col A H D" using collinear_b `bet A H D \<and> col E F H \<and> \<not> col E F A` by blast
				have "col D A H" using collinearorder[OF `col A H D`] by blast
				have "A \<noteq> D" using betweennotequal[OF `bet A H D`] by blast
				have "D \<noteq> A" using inequalitysymmetric[OF `A \<noteq> D`] .
				have "col A F H" using collinear4[OF `col D A F` `col D A H` `D \<noteq> A`] .
				have "col H F A" using collinearorder[OF `col A F H`] by blast
				have "col E F H" using `col E F H` .
				have "col H F E" using collinearorder[OF `col E F H`] by blast
				have "col F A E" using collinear4[OF `col H F A` `col H F E` `H \<noteq> F`] .
				have "col E F A" using collinearorder[OF `col F A E`] by blast
				have "\<not> col E F A" using `\<not> col E F A` .
				show "False" using `\<not> col E F A` `col E F A` by blast
			qed
			hence "H = F" by blast
			have "bet A F D" using `bet A H D` `H = F` by blast
			have "\<not> (col E A F)"
			proof (rule ccontr)
				assume "\<not> (\<not> (col E A F))"
hence "col E A F" by blast
				have "col E F A" using collinearorder[OF `col E A F`] by blast
				show "False" using `col E F A` `bet A H D \<and> col E F H \<and> \<not> col E F A` by blast
			qed
			hence "\<not> col E A F" by blast
			have "triangle E A F" using triangle_b[OF `\<not> col E A F`] .
			have "ang_lt A E F E F D" using Prop16[OF `triangle E A F` `bet A F D`] by blast
			have "ang_eq E F D A E F" using equalanglessymmetric[OF `ang_eq A E F E F D`] .
			have "ang_lt E F D E F D" using angleorderrespectscongruence2[OF `ang_lt A E F E F D` `ang_eq E F D A E F`] .
			have "\<not> (meets A B C D)"
			proof (rule ccontr)
				assume "\<not> (\<not> (meets A B C D))"
hence "meets A B C D" by blast
				have "\<not> (ang_lt E F D E F D)" using angletrichotomy[OF `ang_lt E F D E F D`] .
				show "False" using `\<not> (ang_lt E F D E F D)` `ang_lt E F D E F D` by blast
			qed
			hence "\<not> (meets A B C D)" by blast
			thus ?thesis by blast
		next
			assume "E = G"
			have "col C D E" using `col C D G` `E = G` by blast
			have "col C D F" using collinearorder[OF `col C F D`] by blast
			have "col D E F" using collinear4[OF `col C D E` `col C D F` `C \<noteq> D`] .
			have "col E F D" using collinearorder[OF `col D E F`] by blast
			have "col E F H" using `col E F H` .
			have "\<not> (E \<noteq> F)"
			proof (rule ccontr)
				assume "\<not> (\<not> (E \<noteq> F))"
hence "E \<noteq> F" by blast
				have "col F D H" using collinear4[OF `col E F D` `col E F H` `E \<noteq> F`] .
				have "col D H F" using collinearorder[OF `col F D H`] by blast
				have "col A H D" using collinear_b `bet A H D \<and> col E F H \<and> \<not> col E F A` by blast
				have "col D H A" using collinearorder[OF `col A H D`] by blast
				have "H \<noteq> D" using betweennotequal[OF `bet A H D`] by blast
				have "D \<noteq> H" using inequalitysymmetric[OF `H \<noteq> D`] .
				have "col H F A" using collinear4[OF `col D H F` `col D H A` `D \<noteq> H`] .
				have "col E F H" using `col E F H` .
				have "col H F E" using collinearorder[OF `col E F H`] by blast
				have "\<not> (H \<noteq> F)"
				proof (rule ccontr)
					assume "\<not> (\<not> (H \<noteq> F))"
hence "H \<noteq> F" by blast
					have "col F A E" using collinear4[OF `col H F A` `col H F E` `H \<noteq> F`] .
					have "col E F A" using collinearorder[OF `col F A E`] by blast
					have "\<not> col E F A" using `\<not> col E F A` .
					show "False" using `\<not> col E F A` `col E F A` by blast
				qed
				hence "H = F" by blast
				have "col A H D" using collinear_b `bet A H D \<and> col E F H \<and> \<not> col E F A` by blast
				have "col A F D" using `col A H D` `H = F` by blast
				have "col D F A" using collinearorder[OF `col A F D`] by blast
				have "col D F C" using collinearorder[OF `col C D F`] by blast
				have "H \<noteq> D" using betweennotequal[OF `bet A H D`] by blast
				have "D \<noteq> H" using inequalitysymmetric[OF `H \<noteq> D`] .
				have "D \<noteq> F" using `D \<noteq> H` `H = F` by blast
				have "col F A C" using collinear4[OF `col D F A` `col D F C` `D \<noteq> F`] .
				have "col C F A" using collinearorder[OF `col F A C`] by blast
				have "col C D G" using `col C D G` .
				have "col D C G" using collinearorder[OF `col C D G`] by blast
				have "col C D F" using collinearorder[OF `col C F D`] by blast
				have "col D C F" using collinearorder[OF `col C D F`] by blast
				have "D \<noteq> C" using inequalitysymmetric[OF `C \<noteq> D`] .
				have "col C G F" using collinear4[OF `col D C G` `col D C F` `D \<noteq> C`] .
				have "col C F G" using collinearorder[OF `col C G F`] by blast
				have "\<not> (C \<noteq> F)"
				proof (rule ccontr)
					assume "\<not> (\<not> (C \<noteq> F))"
hence "C \<noteq> F" by blast
					have "col F A G" using collinear4[OF `col C F A` `col C F G` `C \<noteq> F`] .
					have "col F A E" using `col F A G` `E = G` by blast
					have "col E F A" using collinearorder[OF `col F A E`] by blast
					show "False" using `col E F A` `bet A H D \<and> col E F H \<and> \<not> col E F A` by blast
				qed
				hence "C = F" by blast
				have "col A H D" using collinear_b `bet A H D \<and> col E F H \<and> \<not> col E F A` by blast
				have "col A C D" using `col A F D` `C = F` by blast
				have "col C D A" using collinearorder[OF `col A C D`] by blast
				have "col F D A" using `col C D A` `C = F` by blast
				have "col C D E" using `col C D E` by blast
				have "col F D E" using `col C D E` `C = F` by blast
				have "col D F E" using collinearorder[OF `col D E F`] by blast
				have "col D F A" using collinearorder[OF `col A F D`] by blast
				have "D \<noteq> F" using `D \<noteq> C` `C = F` by blast
				have "col F E A" using collinear4[OF `col D F E` `col D F A` `D \<noteq> F`] .
				have "col E F A" using collinearorder[OF `col F E A`] by blast
				show "False" using `col E F A` `bet A H D \<and> col E F H \<and> \<not> col E F A` by blast
			qed
			hence "E = F" by blast
			have "col E F A" using collinear_b `E = F` by blast
			have "\<not> (meets A B C D)"
			proof (rule ccontr)
				assume "\<not> (\<not> (meets A B C D))"
hence "meets A B C D" by blast
				have "\<not> col E F A" using `\<not> col E F A` .
				show "False" using `\<not> col E F A` `col E F A` by blast
			qed
			hence "\<not> (meets A B C D)" by blast
			thus ?thesis by blast
		next
			assume "bet E A G"
			have "E \<noteq> A" using betweennotequal[OF `bet E A G`] by blast
			have "ray_on E A G" using ray4 `bet E A G` `E \<noteq> A` by blast
			have "\<not> (meets A B C D)"
			proof (rule ccontr)
				assume "\<not> (\<not> (meets A B C D))"
hence "meets A B C D" by blast
				have "\<not> (ray_on E A G)" using `\<not> (ray_on E A G)` .
				show "False" using `\<not> (ray_on E A G)` `ray_on E A G` by blast
			qed
			hence "\<not> (meets A B C D)" by blast
			thus ?thesis by blast
		next
			assume "bet A E G"
			have "\<not> (meets A B C D)"
			proof (rule ccontr)
				assume "\<not> (\<not> (meets A B C D))"
hence "meets A B C D" by blast
				have "\<not> (bet A E G)" using `\<not> (bet A E G)` .
				show "False" using `\<not> (bet A E G)` `bet A E G` by blast
			qed
			hence "\<not> (meets A B C D)" by blast
			thus ?thesis by blast
		next
			assume "bet A G E"
			have "bet E G A" using betweennesssymmetryE[OF `bet A G E`] .
			have "E \<noteq> A" using betweennotequal[OF `bet E G A`] by blast
			have "ray_on E A G" using ray4 `bet E G A` `E \<noteq> A` by blast
			have "\<not> (meets A B C D)"
			proof (rule ccontr)
				assume "\<not> (\<not> (meets A B C D))"
hence "meets A B C D" by blast
				have "\<not> (ray_on E A G)" using `\<not> (ray_on E A G)` .
				show "False" using `\<not> (ray_on E A G)` `ray_on E A G` by blast
			qed
			hence "\<not> (meets A B C D)" by blast
			thus ?thesis by blast
		qed
		show "False" using `\<not> (meets A B C D)` `meets A B C D` by blast
	qed
	hence "\<not> (meets A B C D)" by blast
	have "A = A" using equalityreflexiveE.
	have "col A B A" using collinear_b `A = A` by blast
	have "col A B E" using collinear_b `bet A E B` by blast
	have "D = D" using equalityreflexiveE.
	have "col C D D" using collinear_b `D = D` by blast
	have "col C D F" using collinear_b `bet C F D` by blast
	have "A \<noteq> E" using betweennotequal[OF `bet A E B`] by blast
	have "F \<noteq> D" using betweennotequal[OF `bet C F D`] by blast
	have "bet A H D" using `bet A H D` .
	have "bet E H F" using collinearbetween[OF `col A E B` `col C F D` `A \<noteq> B` `C \<noteq> D` `A \<noteq> E` `F \<noteq> D` `\<not> (meets A B C D)` `bet A H D` `col E F H`] .
	have "bet F H E" using betweennesssymmetryE[OF `bet E H F`] .
	have "A \<noteq> B \<and> C \<noteq> D \<and> col A B A \<and> col A B E \<and> A \<noteq> E \<and> col C D F \<and> col C D D \<and> F \<noteq> D \<and> \<not> (meets A B C D) \<and> bet A H D \<and> bet F H E" using `A \<noteq> B` `C \<noteq> D` `col A B A` `col A B E` `A \<noteq> E` `col C D F` `col C D D` `F \<noteq> D` `\<not> (meets A B C D)` `bet A H D \<and> col E F H \<and> \<not> col E F A` `bet F H E` by blast
	have "parallel A B C D" using parallel_b[OF `A \<noteq> B` `C \<noteq> D` `col A B A` `col A B E` `A \<noteq> E` `col C D F` `col C D D` `F \<noteq> D` `\<not> (meets A B C D)` `bet A H D` `bet F H E`] .
	thus ?thesis by blast
qed

end