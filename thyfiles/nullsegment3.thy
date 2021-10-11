theory nullsegment3
	imports Geometry
begin

theorem(in euclidean_geometry) nullsegment3:
	assumes 
		"A \<noteq> B"
		"seg_eq A B C D"
	shows "C \<noteq> D"
proof -
	have "\<not> (C = D)"
	proof (rule ccontr)
		assume "\<not> (C \<noteq> D)"
		hence "C = D" by blast
		have "seg_eq A B C C" using `seg_eq A B C D` `C = D` by blast
		have "A = B" using nullsegment1E[OF `seg_eq A B C C`] .
		have "A \<noteq> B" using `A \<noteq> B` .
		show "False" using `A \<noteq> B` `A = B` by blast
	qed
	hence "C \<noteq> D" by blast
	thus ?thesis by blast
qed

end