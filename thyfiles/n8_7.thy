theory n8_7
	imports n8_2 n8_3 Geometry collinearorder congruenceflip congruencesymmetric congruencetransitive droppedperpendicularunique extensionunique inequalitysymmetric ray4
begin

theorem(in euclidean_geometry) n8_7:
	assumes 
		"ang_right C B A"
	shows "\<not> (ang_right A C B)"
proof -
	have "ang_right A B C" using n8_2[OF `ang_right C B A`] .
	have "B \<noteq> C" using rightangle_f[OF `ang_right A B C`] by blast
	have "C \<noteq> B" using inequalitysymmetric[OF `B \<noteq> C`] .
	obtain E where "bet B C E \<and> seg_eq C E C B" using extensionE[OF `B \<noteq> C` `C \<noteq> B`]  by  blast
	have "bet B C E" using `bet B C E \<and> seg_eq C E C B` by blast
	have "seg_eq C E C B" using `bet B C E \<and> seg_eq C E C B` by blast
	have "col B C E" using collinear_b `bet B C E \<and> seg_eq C E C B` by blast
	have "col E C B" using collinearorder[OF `col B C E`] by blast
	have "ang_right A B C" using n8_2[OF `ang_right C B A`] .
	have "ray_on B C E" using ray4 `bet B C E \<and> seg_eq C E C B` `B \<noteq> C` by blast
	have "ang_right A B E" using n8_3[OF `ang_right A B C` `ray_on B C E`] .
	have "ang_right E B A" using n8_2[OF `ang_right A B E`] .
	have "\<not> (ang_right A C B)"
	proof (rule ccontr)
		assume "\<not> (\<not> (ang_right A C B))"
hence "ang_right A C B" by blast
		have "ang_right B C A" using n8_2[OF `ang_right A C B`] .
		obtain F where "bet B C F \<and> seg_eq B C F C \<and> seg_eq B A F A \<and> C \<noteq> A" using rightangle_f[OF `ang_right B C A`]  by  blast
		have "bet B C F" using `bet B C F \<and> seg_eq B C F C \<and> seg_eq B A F A \<and> C \<noteq> A` by blast
		have "seg_eq B C F C" using `bet B C F \<and> seg_eq B C F C \<and> seg_eq B A F A \<and> C \<noteq> A` by blast
		have "seg_eq B A F A" using `bet B C F \<and> seg_eq B C F C \<and> seg_eq B A F A \<and> C \<noteq> A` by blast
		have "C \<noteq> A" using `bet B C F \<and> seg_eq B C F C \<and> seg_eq B A F A \<and> C \<noteq> A` by blast
		have "seg_eq F C B C" using congruencesymmetric[OF `seg_eq B C F C`] .
		have "seg_eq C F B C" using congruenceflip[OF `seg_eq F C B C`] by blast
		have "seg_eq C E B C" using congruenceflip[OF `seg_eq C E C B`] by blast
		have "seg_eq B C C E" using congruencesymmetric[OF `seg_eq C E B C`] .
		have "seg_eq C F C E" using congruencetransitive[OF `seg_eq C F B C` `seg_eq B C C E`] .
		have "F = E" using extensionunique[OF `bet B C F` `bet B C E` `seg_eq C F C E`] .
		have "bet E C B" using betweennesssymmetryE[OF `bet B C E`] .
		have "seg_eq F A B A" using congruencesymmetric[OF `seg_eq B A F A`] .
		have "seg_eq E A B A" using `seg_eq F A B A` `F = E` by blast
		have "seg_eq E C B C" using congruenceflip[OF `seg_eq C E B C`] by blast
		have "bet E C B \<and> seg_eq E C B C \<and> seg_eq E A B A \<and> C \<noteq> A" using `bet E C B` `seg_eq E C B C` `seg_eq E A B A` `bet B C F \<and> seg_eq B C F C \<and> seg_eq B A F A \<and> C \<noteq> A` by blast
		have "ang_right E C A" using rightangle_b[OF `bet E C B` `seg_eq E C B C` `seg_eq E A B A` `C \<noteq> A`] .
		have "ang_right E B A" using `ang_right E B A` .
		have "C = B" using droppedperpendicularunique[OF `ang_right E C A` `ang_right E B A` `col E C B`] .
		show "False" using `C = B` `C \<noteq> B` by blast
	qed
	hence "\<not> (ang_right A C B)" by blast
	thus ?thesis by blast
qed

end