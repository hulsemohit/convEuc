theory droppedperpendicularunique
	imports n3_7a n3_7b Geometry altitudebisectsbase betweennotequal collinear4 collinearorder collinearright congruenceflip inequalitysymmetric midpointunique rightreverse
begin

theorem(in euclidean_geometry) droppedperpendicularunique:
	assumes 
		"ang_right A M P"
		"ang_right A J P"
		"col A M J"
	shows "M = J"
proof -
	have "\<not> (M \<noteq> J)"
	proof (rule ccontr)
		assume "\<not> (\<not> (M \<noteq> J))"
hence "M \<noteq> J" by blast
		have "J \<noteq> M" using inequalitysymmetric[OF `M \<noteq> J`] .
		obtain E where "bet M J E \<and> seg_eq J E M J" using extensionE[OF `M \<noteq> J` `M \<noteq> J`]  by  blast
		have "bet M J E" using `bet M J E \<and> seg_eq J E M J` by blast
		have "M \<noteq> E" using betweennotequal[OF `bet M J E`] by blast
		obtain F where "bet J M F \<and> seg_eq M F M E" using extensionE[OF `J \<noteq> M` `M \<noteq> E`]  by  blast
		have "seg_eq M F M E" using `bet J M F \<and> seg_eq M F M E` by blast
		have "bet J M F" using `bet J M F \<and> seg_eq M F M E` by blast
		have "bet E J M" using betweennesssymmetryE[OF `bet M J E`] .
		have "bet E J F" using n3_7b[OF `bet E J M` `bet J M F`] .
		have "bet F J E" using betweennesssymmetryE[OF `bet E J F`] .
		have "bet E M F" using n3_7a[OF `bet E J M` `bet J M F`] .
		have "J \<noteq> F" using betweennotequal[OF `bet E J F`] by blast
		have "F \<noteq> J" using inequalitysymmetric[OF `J \<noteq> F`] .
		have "col J M F" using collinear_b `bet J M F \<and> seg_eq M F M E` by blast
		have "col M J F" using collinearorder[OF `col J M F`] by blast
		have "col M J A" using collinearorder[OF `col A M J`] by blast
		have "J \<noteq> M" using betweennotequal[OF `bet E J M`] by blast
		have "M \<noteq> J" using inequalitysymmetric[OF `J \<noteq> M`] .
		have "col J F A" using collinear4[OF `col M J F` `col M J A` `M \<noteq> J`] .
		have "col A J F" using collinearorder[OF `col J F A`] by blast
		have "ang_right F J P" using collinearright[OF `ang_right A J P` `col A J F` `F \<noteq> J`] .
		have "col J M F" using collinear_b `bet J M F \<and> seg_eq M F M E` by blast
		have "col J M A" using collinearorder[OF `col A M J`] by blast
		have "col M F A" using collinear4[OF `col J M F` `col J M A` `J \<noteq> M`] .
		have "col A M F" using collinearorder[OF `col M F A`] by blast
		have "M \<noteq> F" using betweennotequal[OF `bet E M F`] by blast
		have "F \<noteq> M" using inequalitysymmetric[OF `M \<noteq> F`] .
		have "ang_right F M P" using collinearright[OF `ang_right A M P` `col A M F` `F \<noteq> M`] .
		have "seg_eq F M M E" using congruenceflip[OF `seg_eq M F M E`] by blast
		have "ang_right F M P" using collinearright[OF `ang_right A M P` `col A M F` `F \<noteq> M`] .
		have "bet F M E" using betweennesssymmetryE[OF `bet E M F`] .
		have "seg_eq F P E P" using rightreverse[OF `ang_right F M P` `bet F M E` `seg_eq F M M E`] .
		have "midpoint F J E" using altitudebisectsbase[OF `bet F J E` `seg_eq F P E P` `ang_right F J P`] .
		have "bet F M E" using betweennesssymmetryE[OF `bet E M F`] .
		have "seg_eq F M M E" using congruenceflip[OF `seg_eq M F M E`] by blast
		have "midpoint F M E" using midpoint_b[OF `bet F M E` `seg_eq F M M E`] .
		have "J = M" using midpointunique[OF `midpoint F J E` `midpoint F M E`] .
		show "False" using `J = M` `J \<noteq> M` by blast
	qed
	hence "M = J" by blast
	thus ?thesis by blast
qed

end