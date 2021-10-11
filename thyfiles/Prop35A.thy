theory Prop35A
	imports n3_6a n3_6b n35helper EFreflexive ETreflexive Geometry NChelper NCorder PGflip PGrotate PGsymmetric Prop04 Prop29C Prop34 betweennotequal collinear4 collinear5 collinearbetween collinearorder congruenceflip congruencesymmetric congruencetransitive diagonalsmeet differenceofparts equalanglesNC equalangleshelper equalanglesreflexive equalanglessymmetric equalanglestransitive inequalitysymmetric layoffunique lessthancongruence lessthancongruence2 parallelNC paralleldef2B parallelflip parallelsymmetric ray4 samesidesymmetric sumofparts trapezoiddiagonals
begin

theorem(in euclidean_geometry) Prop35A:
	assumes 
		"parallelogram A B C D"
		"parallelogram E B C F"
		"bet A D F"
		"col A E F"
	shows "qua_eq_area A B C D E B C F"
proof -
	have "parallel A B C D \<and> parallel A D B C" using parallelogram_f[OF `parallelogram A B C D`] .
	have "parallel A B C D" using `parallel A B C D \<and> parallel A D B C` by blast
	have "parallel A D B C" using `parallel A B C D \<and> parallel A D B C` by blast
	have "parallel A B D C" using parallelflip[OF `parallel A B C D`] by blast
	have "seg_eq A D B C" using Prop34[OF `parallelogram A B C D`] by blast
	have "seg_eq E F B C" using Prop34[OF `parallelogram E B C F`] by blast
	have "seg_eq B C E F" using congruencesymmetric[OF `seg_eq E F B C`] .
	have "seg_eq A D E F" using congruencetransitive[OF `seg_eq A D B C` `seg_eq B C E F`] .
	have "seg_eq E F F E" using equalityreverseE.
	have "seg_eq A D F E" using congruencetransitive[OF `seg_eq A D E F` `seg_eq E F F E`] .
	have "seg_eq A D A D" using congruencereflexiveE.
	have "seg_lt A D A F" using lessthan_b[OF `bet A D F` `seg_eq A D A D`] .
	have "seg_lt F E A F" using lessthancongruence2[OF `seg_lt A D A F` `seg_eq A D F E`] .
	have "seg_eq A F F A" using equalityreverseE.
	have "seg_lt F E F A" using lessthancongruence[OF `seg_lt F E A F` `seg_eq A F F A`] .
	obtain e where "bet F e A \<and> seg_eq F e F E" using lessthan_f[OF `seg_lt F E F A`]  by  blast
	have "bet F e A" using `bet F e A \<and> seg_eq F e F E` by blast
	have "seg_eq F e F E" using `bet F e A \<and> seg_eq F e F E` by blast
	have "F \<noteq> A" using betweennotequal[OF `bet F e A`] by blast
	have "ray_on F A e" using ray4 `bet F e A \<and> seg_eq F e F E` `F \<noteq> A` by blast
	have "bet A E F" using n35helper[OF `parallelogram A B C D` `parallelogram E B C F` `bet A D F` `col A E F`] .
	have "bet F E A" using betweennesssymmetryE[OF `bet A E F`] .
	have "ray_on F A E" using ray4 `bet F E A` `F \<noteq> A` by blast
	have "e = E" using layoffunique[OF `ray_on F A e` `ray_on F A E` `seg_eq F e F E`] .
	have "bet F E A" using `bet F E A` by blast
	have "bet A E F" using betweennesssymmetryE[OF `bet F E A`] .
	have "parallel D C A B" using parallelsymmetric[OF `parallel A B D C`] .
	have "bet F D A" using betweennesssymmetryE[OF `bet A D F`] .
	have "tarski_parallel A D B C" using paralleldef2B[OF `parallel A D B C`] .
	have "same_side B C A D" using tarski_parallel_f[OF `tarski_parallel A D B C`] by blast
	have "same_side C B D A" using samesidesymmetric[OF `same_side B C A D`] by blast
	have "ang_eq F D C D A B" using Prop29C[OF `parallel D C A B` `same_side C B D A` `bet F D A`] by blast
	have "D = D" using equalityreflexiveE.
	have "C = C" using equalityreflexiveE.
	have "B = B" using equalityreflexiveE.
	have "A = A" using equalityreflexiveE.
	have "\<not> col A D C" using parallelNC[OF `parallel A B D C`] by blast
	have "\<not> (A = D)"
	proof (rule ccontr)
		assume "\<not> (A \<noteq> D)"
		hence "A = D" by blast
		have "col A D C" using collinear_b `A = D` by blast
		show "False" using `col A D C` `\<not> col A D C` by blast
	qed
	hence "A \<noteq> D" by blast
	have "A \<noteq> D" using betweennotequal[OF `bet A D F`] by blast
	have "\<not> col A B C" using parallelNC[OF `parallel A B C D`] by blast
	have "\<not> (A = B)"
	proof (rule ccontr)
		assume "\<not> (A \<noteq> B)"
		hence "A = B" by blast
		have "col A B C" using collinear_b `A = B` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "A \<noteq> B" by blast
	have "ray_on A B B" using ray4 `B = B` `A \<noteq> B` by blast
	have "\<not> (\<not> (bet A D E \<or> bet A E D \<or> D = E))"
	proof (rule ccontr)
		assume "\<not> (\<not> (\<not> (bet A D E \<or> bet A E D \<or> D = E)))"
hence "\<not> (bet A D E \<or> bet A E D \<or> D = E)" by blast
		have "\<not> (bet A D E) \<and> \<not> (bet A E D) \<and> D \<noteq> E" using `\<not> (bet A D E \<or> bet A E D \<or> D = E)` by blast
		have "\<not> (bet A D E)" using `\<not> (bet A D E) \<and> \<not> (bet A E D) \<and> D \<noteq> E` by blast
		have "\<not> (bet A E D)" using `\<not> (bet A D E) \<and> \<not> (bet A E D) \<and> D \<noteq> E` by blast
		have "D \<noteq> E" using `\<not> (bet A D E) \<and> \<not> (bet A E D) \<and> D \<noteq> E` by blast
		have "bet A D F" using `bet A D F` .
		have "bet A E F" using `bet A E F` .
		have "D = E" using connectivityE[OF `bet A D F` `bet A E F` `\<not> (bet A D E)` `\<not> (bet A E D)`] .
		show "False" using `D = E` `\<not> (bet A D E) \<and> \<not> (bet A E D) \<and> D \<noteq> E` by blast
	qed
	hence "bet A D E \<or> bet A E D \<or> D = E" by blast
	consider "bet A D E"|"bet A E D"|"D = E" using `\<not> (\<not> (bet A D E \<or> bet A E D \<or> D = E))`  by blast
	hence "ray_on A D E"
	proof (cases)
		assume "bet A D E"
		have "ray_on A D E" using ray4 `bet A D E` `A \<noteq> D` by blast
		thus ?thesis by blast
	next
		assume "bet A E D"
		have "ray_on A D E" using ray4 `bet A E D` `A \<noteq> D` by blast
		thus ?thesis by blast
	next
		assume "D = E"
		have "A \<noteq> D" using `A \<noteq> D` .
		have "ray_on A D D" using ray4 `D = D` `A \<noteq> D` by blast
		have "ray_on A D E" using `ray_on A D D` `D = E` by blast
		thus ?thesis by blast
	qed
	have "\<not> col A D B" using parallelNC[OF `parallel A D B C`] by blast
	have "\<not> col D A B" using NCorder[OF `\<not> col A D B`] by blast
	have "ang_eq D A B D A B" using equalanglesreflexive[OF `\<not> col D A B`] .
	have "ang_eq D A B E A B" using equalangleshelper[OF `ang_eq D A B D A B` `ray_on A D E` `ray_on A B B`] .
	have "ang_eq F D C E A B" using equalanglestransitive[OF `ang_eq F D C D A B` `ang_eq D A B E A B`] .
	have "seg_eq A B D C" using Prop34[OF `parallelogram A B C D`] by blast
	have "seg_eq D E E D" using equalityreverseE.
	consider "bet A D E"|"bet A E D"|"D = E" using `\<not> (\<not> (bet A D E \<or> bet A E D \<or> D = E))`  by blast
	hence "seg_eq A E D F"
	proof (cases)
		assume "bet A D E"
		have "bet D E F" using n3_6a[OF `bet A D E` `bet A E F`] .
		have "bet F E D" using betweennesssymmetryE[OF `bet D E F`] .
		have "seg_eq A E F D" using sumofparts[OF `seg_eq A D F E` `seg_eq D E E D` `bet A D E` `bet F E D`] .
		have "seg_eq A E D F" using congruenceflip[OF `seg_eq A E F D`] by blast
		thus ?thesis by blast
	next
		assume "bet A E D"
		have "bet D E A" using betweennesssymmetryE[OF `bet A E D`] .
		have "bet E D F" using n3_6a[OF `bet A E D` `bet A D F`] .
		have "seg_eq A D F E" using `seg_eq A D F E` .
		have "seg_eq D A E F" using congruenceflip[OF `seg_eq A D E F`] by blast
		have "seg_eq E A D F" using differenceofparts[OF `seg_eq D E E D` `seg_eq D A E F` `bet D E A` `bet E D F`] .
		have "seg_eq A E D F" using congruenceflip[OF `seg_eq E A D F`] by blast
		thus ?thesis by blast
	next
		assume "D = E"
		have "seg_eq A D E F" using `seg_eq A D E F` .
		have "seg_eq A E E F" using `seg_eq A D E F` `D = E` by blast
		have "seg_eq A E D F" using `seg_eq A D E F` `D = E` `D = E` by blast
		thus ?thesis by blast
	qed
	have "seg_eq D F A E" using congruencesymmetric[OF `seg_eq A E D F`] .
	have "seg_eq D C A B" using congruencesymmetric[OF `seg_eq A B D C`] .
	have "seg_eq F C E B \<and> ang_eq D F C A E B \<and> ang_eq D C F A B E" using Prop04[OF `seg_eq D F A E` `seg_eq D C A B` `ang_eq F D C E A B`] .
	have "seg_eq F C E B" using `seg_eq F C E B \<and> ang_eq D F C A E B \<and> ang_eq D C F A B E` by blast
	have "seg_eq F D E A" using congruenceflip[OF `seg_eq D F A E`] by blast
	have "ang_eq D C F A B E" using `seg_eq F C E B \<and> ang_eq D F C A E B \<and> ang_eq D C F A B E` by blast
	have "ang_eq A B E D C F" using equalanglessymmetric[OF `ang_eq D C F A B E`] .
	have "\<not> col D C F" using equalanglesNC[OF `ang_eq A B E D C F`] .
	have "\<not> col F D C" using NCorder[OF `\<not> col D C F`] by blast
	have "triangle F D C" using triangle_b[OF `\<not> col F D C`] .
	have "seg_eq F D E A \<and> seg_eq D C A B \<and> seg_eq F C E B \<and> triangle F D C" using `seg_eq F D E A` `seg_eq D C A B` `seg_eq F C E B \<and> ang_eq D F C A E B \<and> ang_eq D C F A B E` `triangle F D C` by blast
	have "tri_cong F D C E A B" using trianglecongruence_b[OF `seg_eq F D E A` `seg_eq D C A B` `seg_eq F C E B` `triangle F D C`] .
	have "tri_eq_area F D C E A B" using congruentequalE[OF `tri_cong F D C E A B`] .
	consider "bet A D E"|"bet A E D"|"D = E" using `\<not> (\<not> (bet A D E \<or> bet A E D \<or> D = E))`  by blast
	hence "qua_eq_area A B C D E B C F"
	proof (cases)
		assume "bet A D E"
		have "parallelogram A B C D" using `parallelogram A B C D` .
		obtain M where "bet A M C \<and> bet B M D" using diagonalsmeet[OF `parallelogram A B C D`]  by  blast
		have "bet B M D" using `bet A M C \<and> bet B M D` by blast
		have "bet D M B" using betweennesssymmetryE[OF `bet B M D`] .
		have "\<not> col A D B" using parallelNC[OF `parallel A D B C`] by blast
		have "col A D E" using collinear_b `bet A D E` by blast
		have "col A D A" using collinear_b `A = A` by blast
		have "A \<noteq> E" using betweennotequal[OF `bet A D E`] by blast
		have "\<not> col A E B" using NChelper[OF `\<not> col A D B` `col A D A` `col A D E` `A \<noteq> E`] .
		have "bet B M D" using betweennesssymmetryE[OF `bet D M B`] .
		have "bet A M C" using `bet A M C \<and> bet B M D` by blast
		obtain H where "bet B H E \<and> bet A M H" using Pasch_outerE[OF `bet B M D` `bet A D E` `\<not> col A E B`]  by  blast
		have "bet B H E" using `bet B H E \<and> bet A M H` by blast
		have "bet A M H" using `bet B H E \<and> bet A M H` by blast
		have "col A M H" using collinear_b `bet B H E \<and> bet A M H` by blast
		have "col A M C" using collinear_b `bet A M C \<and> bet B M D` by blast
		have "A \<noteq> M" using betweennotequal[OF `bet A M C`] by blast
		have "M \<noteq> A" using inequalitysymmetric[OF `A \<noteq> M`] .
		have "col M A H" using collinearorder[OF `col A M H`] by blast
		have "col M A C" using collinearorder[OF `col A M C`] by blast
		have "col A H C" using collinear4[OF `col M A H` `col M A C` `M \<noteq> A`] .
		have "bet E H B" using betweennesssymmetryE[OF `bet B H E`] .
		have "E \<noteq> A" using inequalitysymmetric[OF `A \<noteq> E`] .
		have "\<not> (B = C)"
		proof (rule ccontr)
			assume "\<not> (B \<noteq> C)"
			hence "B = C" by blast
			have "col A B C" using collinear_b `B = C` by blast
			show "False" using `col A B C` `\<not> col A B C` by blast
		qed
		hence "B \<noteq> C" by blast
		have "\<not> (meets A D B C)" using parallel_f[OF `parallel A D B C`] by fastforce
		have "\<not> (meets E A C B)"
		proof (rule ccontr)
			assume "\<not> (\<not> (meets E A C B))"
hence "meets E A C B" by blast
			obtain q where "E \<noteq> A \<and> C \<noteq> B \<and> col E A q \<and> col C B q" using meet_f[OF `meets E A C B`]  by  blast
			have "E \<noteq> A" using `E \<noteq> A` .
			have "C \<noteq> B" using `E \<noteq> A \<and> C \<noteq> B \<and> col E A q \<and> col C B q` by blast
			have "B \<noteq> C" using inequalitysymmetric[OF `C \<noteq> B`] .
			have "col E A q" using `E \<noteq> A \<and> C \<noteq> B \<and> col E A q \<and> col C B q` by blast
			have "col C B q" using `E \<noteq> A \<and> C \<noteq> B \<and> col E A q \<and> col C B q` by blast
			have "col B C q" using collinearorder[OF `col C B q`] by blast
			have "col A E q" using collinearorder[OF `col E A q`] by blast
			have "col A D E" using collinear_b `bet A D E` by blast
			have "col E A D" using collinearorder[OF `col A D E`] by blast
			have "col E A q" using collinearorder[OF `col A E q`] by blast
			have "A \<noteq> D" using betweennotequal[OF `bet A D E`] by blast
			have "col A D q" using collinear4[OF `col E A D` `col E A q` `E \<noteq> A`] .
			have "A \<noteq> D \<and> B \<noteq> C \<and> col A D q \<and> col B C q" using `A \<noteq> D` `B \<noteq> C` `col A D q` `col B C q` by blast
			have "meets A D B C" using meet_b[OF `A \<noteq> D` `B \<noteq> C` `col A D q` `col B C q`] .
			show "False" using `meets A D B C` `\<not> (meets A D B C)` by blast
		qed
		hence "\<not> (meets E A C B)" by blast
		have "bet E H B" using `bet E H B` .
		have "col A H C" using `col A H C` .
		have "col A C H" using collinearorder[OF `col A H C`] by blast
		have "col E A A" using collinear_b `A = A` by blast
		have "col C C B" using collinear_b `C = C` by blast
		have "E \<noteq> A" using `E \<noteq> A` .
		have "A \<noteq> E" using `A \<noteq> E` .
		have "B \<noteq> C" using `B \<noteq> C` .
		have "C \<noteq> B" using inequalitysymmetric[OF `B \<noteq> C`] .
		have "bet A H C" using collinearbetween[OF `col E A A` `col C C B` `E \<noteq> A` `C \<noteq> B` `E \<noteq> A` `C \<noteq> B` `\<not> (meets E A C B)` `bet E H B` `col A C H`] .
		have "bet C H A" using betweennesssymmetryE[OF `bet A H C`] .
		have "bet E D A" using betweennesssymmetryE[OF `bet A D E`] .
		have "\<not> col A D C" using parallelNC[OF `parallel A B D C`] by blast
		have "col A D E" using collinear_b `bet A D E` by blast
		have "\<not> col A E C" using NChelper[OF `\<not> col A D C` `col A D A` `col A D E` `A \<noteq> E`] .
		have "\<not> col C A E" using NCorder[OF `\<not> col A E C`] by blast
		obtain G where "bet C G D \<and> bet E G H" using Pasch_innerE[OF `bet C H A` `bet E D A` `\<not> col C A E`]  by  blast
		have "bet E G H" using `bet C G D \<and> bet E G H` by blast
		have "bet E H B" using `bet E H B` .
		have "bet E G B" using n3_6b[OF `bet E G H` `bet E H B`] .
		have "bet E G H" using `bet E G H` .
		have "bet E H B" using `bet E H B` .
		have "bet E G B" using n3_6b[OF `bet E G H` `bet E H B`] .
		have "col E G B" using collinear_b `bet E G B` by blast
		have "\<not> (col D E G)"
		proof (rule ccontr)
			assume "\<not> (\<not> (col D E G))"
hence "col D E G" by blast
			have "col G E D" using collinearorder[OF `col D E G`] by blast
			have "col G E B" using collinearorder[OF `col E G B`] by blast
			have "E \<noteq> G" using betweennotequal[OF `bet E G B`] by blast
			have "G \<noteq> E" using inequalitysymmetric[OF `E \<noteq> G`] .
			have "col E D B" using collinear4[OF `col G E D` `col G E B` `G \<noteq> E`] .
			have "col B C B" using collinear_b `B = B` by blast
			have "col E D A" using collinearorder[OF `col A D E`] by blast
			have "col E D D" using collinear_b `D = D` by blast
			have "D \<noteq> E" using betweennotequal[OF `bet A D E`] by blast
			have "E \<noteq> D" using inequalitysymmetric[OF `D \<noteq> E`] .
			have "col A D B" using collinear5[OF `E \<noteq> D` `col E D A` `col E D D` `col E D B`] .
			have "A \<noteq> D \<and> B \<noteq> C \<and> col A D B \<and> col B C B" using `A \<noteq> D` `B \<noteq> C` `col A D B` `col B C B` by blast
			have "meets A D B C" using meet_b[OF `A \<noteq> D` `B \<noteq> C` `col A D B` `col B C B`] .
			have "\<not> (meets A D B C)" using `\<not> (meets A D B C)` .
			show "False" using `\<not> (meets A D B C)` `meets A D B C` by blast
		qed
		hence "\<not> col D E G" by blast
		have "triangle D E G" using triangle_b[OF `\<not> col D E G`] .
		have "tri_eq_area D E G D E G" using ETreflexive[OF `triangle D E G`] .
		have "tri_eq_area D E G E D G" using ETpermutationE[OF `tri_eq_area D E G D E G`] by blast
		have "tri_eq_area F D C E A B" using `tri_eq_area F D C E A B` .
		have "tri_eq_area F D C A E B" using ETpermutationE[OF `tri_eq_area F D C E A B`] by blast
		have "tri_eq_area A E B F D C" using ETsymmetricE[OF `tri_eq_area F D C A E B`] .
		have "bet B G E" using betweennesssymmetryE[OF `bet E G B`] .
		have "bet C G D" using `bet C G D \<and> bet E G H` by blast
		have "bet A D E" using `bet A D E` .
		have "bet D E F" using n3_6a[OF `bet A D E` `bet A E F`] .
		have "bet F E D" using betweennesssymmetryE[OF `bet D E F`] .
		have "qua_eq_area A D G B F E G C" using cutoff1E[OF `bet A D E` `bet F E D` `bet B G E` `bet C G D` `tri_eq_area D E G E D G` `tri_eq_area A E B F D C`] .
		have "\<not> col D E G" using `\<not> col D E G` .
		have "\<not> col E G D" using NCorder[OF `\<not> col D E G`] by blast
		have "col E G B" using `col E G B` .
		have "G = G" using equalityreflexiveE.
		have "col E G G" using collinear_b `G = G` by blast
		have "G \<noteq> B" using betweennotequal[OF `bet E G B`] by blast
		have "B \<noteq> G" using inequalitysymmetric[OF `G \<noteq> B`] .
		have "\<not> col B G D" using NChelper[OF `\<not> col E G D` `col E G B` `col E G G` `B \<noteq> G`] .
		have "\<not> col D G B" using NCorder[OF `\<not> col B G D`] by blast
		have "col C G D" using collinear_b `bet C G D \<and> bet E G H` by blast
		have "col D G C" using collinearorder[OF `col C G D`] by blast
		have "col D G G" using collinear_b `G = G` by blast
		have "C \<noteq> G" using betweennotequal[OF `bet C G D`] by blast
		have "\<not> col C G B" using NChelper[OF `\<not> col D G B` `col D G C` `col D G G` `C \<noteq> G`] .
		have "\<not> col G C B" using NCorder[OF `\<not> col C G B`] by blast
		have "triangle G C B" using triangle_b[OF `\<not> col G C B`] .
		have "tri_eq_area G C B G C B" using ETreflexive[OF `triangle G C B`] .
		have "tri_eq_area G C B G B C" using ETpermutationE[OF `tri_eq_area G C B G C B`] by blast
		have "qua_eq_area A D G B F E G C" using `qua_eq_area A D G B F E G C` .
		have "bet C G D" using `bet C G D` .
		have "bet D G C" using betweennesssymmetryE[OF `bet C G D`] .
		have "parallelogram B C D A" using PGrotate[OF `parallelogram A B C D`] .
		have "parallelogram D A B C" using PGsymmetric[OF `parallelogram B C D A`] .
		have "parallelogram A D C B" using PGflip[OF `parallelogram D A B C`] .
		obtain q where "bet A q C \<and> bet D q B" using diagonalsmeet[OF `parallelogram A D C B`]  by  blast
		have "bet A q C" using `bet A q C \<and> bet D q B` by blast
		have "bet D q B" using `bet A q C \<and> bet D q B` by blast
		have "parallelogram B C F E" using PGrotate[OF `parallelogram E B C F`] .
		have "parallelogram C F E B" using PGrotate[OF `parallelogram B C F E`] .
		have "parallelogram F E B C" using PGrotate[OF `parallelogram C F E B`] .
		obtain m where "bet F m B \<and> bet E m C" using diagonalsmeet[OF `parallelogram F E B C`]  by  blast
		have "bet F m B" using `bet F m B \<and> bet E m C` by blast
		have "bet E m C" using `bet F m B \<and> bet E m C` by blast
		have "qua_eq_area A D C B F E B C" using paste2E[OF `bet D G C` `bet E G B` `tri_eq_area G C B G B C` `qua_eq_area A D G B F E G C` `bet A M C` `bet D M B` `bet F m B` `bet E m C`] .
		have "qua_eq_area A D C B E B C F" using EFpermutationE[OF `qua_eq_area A D C B F E B C`] by blast
		have "qua_eq_area E B C F A D C B" using EFsymmetricE[OF `qua_eq_area A D C B E B C F`] .
		have "qua_eq_area E B C F A B C D" using EFpermutationE[OF `qua_eq_area E B C F A D C B`] by blast
		have "qua_eq_area A B C D E B C F" using EFsymmetricE[OF `qua_eq_area E B C F A B C D`] .
		thus ?thesis by blast
	next
		assume "bet A E D"
		have "tri_eq_area F D C E A B" using `tri_eq_area F D C E A B` .
		have "tri_eq_area E A B F D C" using ETsymmetricE[OF `tri_eq_area F D C E A B`] .
		have "tri_eq_area E A B D F C" using ETpermutationE[OF `tri_eq_area E A B F D C`] by blast
		obtain H where "bet B H D \<and> bet C H E" using trapezoiddiagonals[OF `parallelogram A B C D` `bet A E D`]  by  blast
		have "bet B H D" using `bet B H D \<and> bet C H E` by blast
		have "bet C H E" using `bet B H D \<and> bet C H E` by blast
		have "bet E H C" using betweennesssymmetryE[OF `bet C H E`] .
		have "\<not> (col B E D)"
		proof (rule ccontr)
			assume "\<not> (\<not> (col B E D))"
hence "col B E D" by blast
			have "col A E D" using collinear_b `bet A E D` by blast
			have "col E D A" using collinearorder[OF `col A E D`] by blast
			have "col E D B" using collinearorder[OF `col B E D`] by blast
			have "E \<noteq> D" using betweennotequal[OF `bet A E D`] by blast
			have "col D A B" using collinear4[OF `col E D A` `col E D B` `E \<noteq> D`] .
			have "col A D B" using collinearorder[OF `col D A B`] by blast
			have "B = B" using equalityreflexiveE.
			have "col B C B" using collinear_b `B = B` by blast
			have "A \<noteq> D" using parallel_f[OF `parallel A D B C`] by fastforce
			have "B \<noteq> C" using parallel_f[OF `parallel A D B C`] by fastforce
			have "meets A D B C" using meet_b[OF `A \<noteq> D` `B \<noteq> C` `col A D B` `col B C B`] .
			have "\<not> (meets A D B C)" using parallel_f[OF `parallel A D B C`] by fastforce
			show "False" using `\<not> (meets A D B C)` `meets A D B C` by blast
		qed
		hence "\<not> col B E D" by blast
		have "qua_eq_area B E D C B E D C" using EFreflexive[OF `bet B H D` `bet E H C` `\<not> col B E D`] .
		have "qua_eq_area B E D C C D E B" using EFpermutationE[OF `qua_eq_area B E D C B E D C`] by blast
		have "qua_eq_area C D E B B E D C" using EFsymmetricE[OF `qua_eq_area B E D C C D E B`] .
		have "bet D E A" using betweennesssymmetryE[OF `bet A E D`] .
		have "bet E D F" using n3_6a[OF `bet A E D` `bet A D F`] .
		have "parallelogram C D A B" using PGsymmetric[OF `parallelogram A B C D`] .
		obtain p where "bet C p A \<and> bet D p B" using diagonalsmeet[OF `parallelogram C D A B`]  by  blast
		have "bet C p A" using `bet C p A \<and> bet D p B` by blast
		have "bet D p B" using `bet C p A \<and> bet D p B` by blast
		have "parallelogram B E F C" using PGflip[OF `parallelogram E B C F`] .
		obtain m where "bet B m F \<and> bet E m C" using diagonalsmeet[OF `parallelogram B E F C`]  by  blast
		have "bet B m F" using `bet B m F \<and> bet E m C` by blast
		have "bet E m C" using `bet B m F \<and> bet E m C` by blast
		have "qua_eq_area C D A B B E F C" using paste2E[OF `bet D E A` `bet E D F` `tri_eq_area E A B D F C` `qua_eq_area C D E B B E D C` `bet C p A` `bet D p B` `bet B m F` `bet E m C`] .
		have "qua_eq_area C D A B E B C F" using EFpermutationE[OF `qua_eq_area C D A B B E F C`] by blast
		have "qua_eq_area E B C F C D A B" using EFsymmetricE[OF `qua_eq_area C D A B E B C F`] .
		have "qua_eq_area E B C F A B C D" using EFpermutationE[OF `qua_eq_area E B C F C D A B`] by blast
		have "qua_eq_area A B C D E B C F" using EFsymmetricE[OF `qua_eq_area E B C F A B C D`] .
		thus ?thesis by blast
	next
		assume "D = E"
		have "tri_eq_area F D C E A B" using `tri_eq_area F D C E A B` .
		have "tri_eq_area F D C B E A" using ETpermutationE[OF `tri_eq_area F D C E A B`] by blast
		have "tri_eq_area B E A F D C" using ETsymmetricE[OF `tri_eq_area F D C B E A`] .
		have "tri_eq_area B E A C D F" using ETpermutationE[OF `tri_eq_area B E A F D C`] by blast
		have "\<not> col D B C" using parallelNC[OF `parallel A D B C`] by blast
		have "\<not> col E B C" using `\<not> col D B C` `D = E` by blast
		have "\<not> col B E C" using NCorder[OF `\<not> col E B C`] by blast
		have "triangle B E C" using triangle_b[OF `\<not> col B E C`] .
		have "tri_eq_area B E C B E C" using ETreflexive[OF `triangle B E C`] .
		have "tri_eq_area B E C C E B" using ETpermutationE[OF `tri_eq_area B E C B E C`] by blast
		have "tri_eq_area B E C C D B" using `tri_eq_area B E C C E B` `D = E` by blast
		have "parallelogram A B C E" using `parallelogram A B C D` `D = E` by blast
		obtain M where "bet A M C \<and> bet B M E" using diagonalsmeet[OF `parallelogram A B C E`]  by  blast
		have "bet A M C" using `bet A M C \<and> bet B M E` by blast
		have "bet B M E" using `bet A M C \<and> bet B M E` by blast
		have "bet E M B" using betweennesssymmetryE[OF `bet B M E`] .
		have "col E M B" using collinear_b `bet E M B` by blast
		have "col B E M" using collinearorder[OF `col E M B`] by blast
		have "parallel A E B C" using parallelogram_f[OF `parallelogram A B C E`] by blast
		have "\<not> col A E B" using parallelNC[OF `parallel A E B C`] by blast
		have "\<not> col B E A" using NCorder[OF `\<not> col A E B`] by blast
		have "oppo_side A B E C" using oppositeside_b[OF `bet A M C` `col B E M` `\<not> col B E A`] .
		have "parallelogram D B C F" using `parallelogram E B C F` `D = E` by blast
		have "\<not> col C D F" using NCorder[OF `\<not> col D C F`] by blast
		obtain m where "bet D m C \<and> bet B m F" using diagonalsmeet[OF `parallelogram D B C F`]  by  blast
		have "bet D m C" using `bet D m C \<and> bet B m F` by blast
		have "bet B m F" using `bet D m C \<and> bet B m F` by blast
		have "bet F m B" using betweennesssymmetryE[OF `bet B m F`] .
		have "col D m C" using collinear_b `bet D m C \<and> bet B m F` by blast
		have "col C D m" using collinearorder[OF `col D m C`] by blast
		have "oppo_side F C D B" using oppositeside_b[OF `bet F m B` `col C D m` `\<not> col C D F`] .
		obtain J where "bet A J C \<and> bet B J D" using diagonalsmeet[OF `parallelogram A B C D`]  by  blast
		have "bet A J C" using `bet A J C \<and> bet B J D` by blast
		have "bet B J D" using `bet A J C \<and> bet B J D` by blast
		have "bet B J E" using `bet B J D` `D = E` by blast
		obtain j where "bet E j C \<and> bet B j F" using diagonalsmeet[OF `parallelogram E B C F`]  by  blast
		have "bet E j C" using `bet E j C \<and> bet B j F` by blast
		have "bet D j C" using `bet E j C` `D = E` by blast
		have "bet C j D" using betweennesssymmetryE[OF `bet D j C`] .
		have "bet B j F" using `bet E j C \<and> bet B j F` by blast
		have "bet F j B" using betweennesssymmetryE[OF `bet B j F`] .
		have "qua_eq_area B A E C C F D B" using paste3E `tri_eq_area B E A C D F` `tri_eq_area B E C C D B` `bet A J C \<and> bet B J D` `bet B J E` `bet F j B` `bet C j D` by blast
		have "qua_eq_area B A E C D B C F" using EFpermutationE[OF `qua_eq_area B A E C C F D B`] by blast
		have "qua_eq_area B A E C E B C F" using `qua_eq_area B A E C D B C F` `D = E` by blast
		have "qua_eq_area E B C F B A E C" using EFsymmetricE[OF `qua_eq_area B A E C E B C F`] .
		have "qua_eq_area E B C F A B C E" using EFpermutationE[OF `qua_eq_area E B C F B A E C`] by blast
		have "qua_eq_area E B C F A B C D" using `qua_eq_area E B C F A B C E` `D = E` by blast
		have "qua_eq_area A B C D E B C F" using EFsymmetricE[OF `qua_eq_area E B C F A B C D`] .
		thus ?thesis by blast
	qed
	thus ?thesis by blast
qed

end