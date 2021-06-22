theory samesidereflexive
	imports Axioms Definitions Theorems
begin

theorem samesidereflexive:
	assumes: `axioms`
		"\<not> col A B P"
	shows: "same_side P P A B"
proof -
	have "A = A" using equalityreflexiveE[OF `axioms`] .
	have "\<not> (P = A)"
	proof (rule ccontr)
		assume "P = A"
		have "col A B A" using col_b `axioms` `A = A` by blast
		have "col A B P" sorry
		show "False" using `col A B P` `\<not> col A B P` by blast
	qed
	hence "P \<noteq> A" by blast
	have "A \<noteq> P" using inequalitysymmetric[OF `axioms` `P \<noteq> A`] .
	obtain C where "bet P A C \<and> seg_eq A C A P" using extensionE[OF `axioms` `P \<noteq> A` `A \<noteq> P`]  by  blast
	have "bet P A C" using `bet P A C \<and> seg_eq A C A P` by blast
	have "col A B A" using col_b `axioms` `A = A` by blast
	have "same_side P P A B" sorry
	thus ?thesis by blast
qed

end