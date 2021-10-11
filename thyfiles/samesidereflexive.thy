theory samesidereflexive
	imports Geometry inequalitysymmetric
begin

theorem(in euclidean_geometry) samesidereflexive:
	assumes 
		"\<not> col A B P"
	shows "same_side P P A B"
proof -
	have "A = A" using equalityreflexiveE.
	have "\<not> (P = A)"
	proof (rule ccontr)
		assume "\<not> (P \<noteq> A)"
		hence "P = A" by blast
		have "col A B A" using collinear_b `A = A` by blast
		have "col A B P" using `col A B A` `P = A` by blast
		show "False" using `col A B P` `\<not> col A B P` by blast
	qed
	hence "P \<noteq> A" by blast
	have "A \<noteq> P" using inequalitysymmetric[OF `P \<noteq> A`] .
	obtain C where "bet P A C \<and> seg_eq A C A P" using extensionE[OF `P \<noteq> A` `A \<noteq> P`]  by  blast
	have "bet P A C" using `bet P A C \<and> seg_eq A C A P` by blast
	have "col A B A" using collinear_b `A = A` by blast
	have "same_side P P A B" using sameside_b[OF `col A B A` `col A B A` `bet P A C` `bet P A C` `\<not> col A B P` `\<not> col A B P`] .
	thus ?thesis by blast
qed

end