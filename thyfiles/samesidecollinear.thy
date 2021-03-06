theory samesidecollinear
	imports Geometry NCdistinct NChelper collinear4 collinearorder inequalitysymmetric
begin

theorem(in euclidean_geometry) samesidecollinear:
	assumes 
		"same_side P Q A B"
		"col A B C"
		"A \<noteq> C"
	shows "same_side P Q A C"
proof -
	obtain p q r where "col A B p \<and> col A B q \<and> bet P p r \<and> bet Q q r \<and> \<not> col A B P \<and> \<not> col A B Q" using sameside_f[OF `same_side P Q A B`]  by  blast
	have "col A B p" using `col A B p \<and> col A B q \<and> bet P p r \<and> bet Q q r \<and> \<not> col A B P \<and> \<not> col A B Q` by blast
	have "col A B q" using `col A B p \<and> col A B q \<and> bet P p r \<and> bet Q q r \<and> \<not> col A B P \<and> \<not> col A B Q` by blast
	have "bet P p r" using `col A B p \<and> col A B q \<and> bet P p r \<and> bet Q q r \<and> \<not> col A B P \<and> \<not> col A B Q` by blast
	have "bet Q q r" using `col A B p \<and> col A B q \<and> bet P p r \<and> bet Q q r \<and> \<not> col A B P \<and> \<not> col A B Q` by blast
	have "\<not> col A B P" using `col A B p \<and> col A B q \<and> bet P p r \<and> bet Q q r \<and> \<not> col A B P \<and> \<not> col A B Q` by blast
	have "\<not> col A B Q" using `col A B p \<and> col A B q \<and> bet P p r \<and> bet Q q r \<and> \<not> col A B P \<and> \<not> col A B Q` by blast
	have "A \<noteq> B" using NCdistinct[OF `\<not> col A B P`] by blast
	have "A = A" using equalityreflexiveE.
	have "col A B A" using collinear_b `A = A` by blast
	have "\<not> col A C P" using NChelper[OF `\<not> col A B P` `col A B A` `col A B C` `A \<noteq> C`] .
	have "\<not> col A C Q" using NChelper[OF `\<not> col A B Q` `col A B A` `col A B C` `A \<noteq> C`] .
	have "col B A p" using collinearorder[OF `col A B p`] by blast
	have "col B A C" using collinearorder[OF `col A B C`] by blast
	have "B \<noteq> A" using inequalitysymmetric[OF `A \<noteq> B`] .
	have "col A C p" using collinear4[OF `col B A C` `col B A p` `B \<noteq> A`] .
	have "col B A q" using collinearorder[OF `col A B q`] by blast
	have "col A C q" using collinear4[OF `col B A C` `col B A q` `B \<noteq> A`] .
	have "same_side P Q A C" using sameside_b[OF `col A C p` `col A C q` `bet P p r` `bet Q q r` `\<not> col A C P` `\<not> col A C Q`] .
	thus ?thesis by blast
qed

end