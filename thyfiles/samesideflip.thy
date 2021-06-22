theory samesideflip
	imports Axioms Definitions Theorems
begin

theorem samesideflip:
	assumes: `axioms`
		"same_side P Q A B"
	shows: "same_side P Q B A"
proof -
	obtain p q r where "col A B p \<and> col A B q \<and> bet P p r \<and> bet Q q r \<and> \<not> col A B P \<and> \<not> col A B Q" using sameside_f[OF `axioms` `same_side P Q A B`] by blast
	have "col A B p" using `col A B p \<and> col A B q \<and> bet P p r \<and> bet Q q r \<and> \<not> col A B P \<and> \<not> col A B Q` by blast
	have "col A B q" using `col A B p \<and> col A B q \<and> bet P p r \<and> bet Q q r \<and> \<not> col A B P \<and> \<not> col A B Q` by blast
	have "bet P p r" using `col A B p \<and> col A B q \<and> bet P p r \<and> bet Q q r \<and> \<not> col A B P \<and> \<not> col A B Q` by blast
	have "bet Q q r" using `col A B p \<and> col A B q \<and> bet P p r \<and> bet Q q r \<and> \<not> col A B P \<and> \<not> col A B Q` by blast
	have "\<not> col A B P" using `col A B p \<and> col A B q \<and> bet P p r \<and> bet Q q r \<and> \<not> col A B P \<and> \<not> col A B Q` by blast
	have "\<not> col A B Q" using `col A B p \<and> col A B q \<and> bet P p r \<and> bet Q q r \<and> \<not> col A B P \<and> \<not> col A B Q` by blast
	have "col B A p" using collinearorder[OF `axioms` `col A B p`] by blast
	have "col B A q" using collinearorder[OF `axioms` `col A B q`] by blast
	have "\<not> col B A P" using NCorder[OF `axioms` `\<not> col A B P`] by blast
	have "\<not> col B A Q" using NCorder[OF `axioms` `\<not> col A B Q`] by blast
	have "same_side P Q B A" using sameside_b[OF `axioms` `col B A p` `col B A q` `bet P p r` `bet Q q r` `\<not> col B A P` `\<not> col B A Q`] .
	thus ?thesis by blast
qed

end