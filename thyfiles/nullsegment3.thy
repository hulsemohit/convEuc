theory nullsegment3
	imports Axioms Definitions Theorems
begin

theorem nullsegment3:
	assumes: `axioms`
		"A \<noteq> B"
		"seg_eq A B C D"
	shows: "C \<noteq> D"
proof -
	have "\<not> (C = D)"
	proof (rule ccontr)
		assume "C = D"
		have "seg_eq A B C C" using `seg_eq A B C D` `C = D` by blast
		have "A = B" using nullsegment1E[OF `axioms` `seg_eq A B C C`] .
		have "A \<noteq> B" using `A \<noteq> B` .
		show "False" using `A \<noteq> B` `A = B` by blast
	qed
	hence "C \<noteq> D" by blast
	thus ?thesis by blast
qed

end