theory samesidesymmetric
	imports Geometry NCorder collinearorder
begin

theorem(in euclidean_geometry) samesidesymmetric:
	assumes 
		"same_side P Q A B"
	shows "same_side Q P A B \<and> same_side P Q B A \<and> same_side Q P B A"
proof -
	obtain E F G where "col A B E \<and> col A B F \<and> bet P E G \<and> bet Q F G \<and> \<not> col A B P \<and> \<not> col A B Q" using sameside_f[OF `same_side P Q A B`]  by  blast
	have "col A B E" using `col A B E \<and> col A B F \<and> bet P E G \<and> bet Q F G \<and> \<not> col A B P \<and> \<not> col A B Q` by blast
	have "col A B F" using `col A B E \<and> col A B F \<and> bet P E G \<and> bet Q F G \<and> \<not> col A B P \<and> \<not> col A B Q` by blast
	have "bet P E G" using `col A B E \<and> col A B F \<and> bet P E G \<and> bet Q F G \<and> \<not> col A B P \<and> \<not> col A B Q` by blast
	have "bet Q F G" using `col A B E \<and> col A B F \<and> bet P E G \<and> bet Q F G \<and> \<not> col A B P \<and> \<not> col A B Q` by blast
	have "\<not> col A B P" using `col A B E \<and> col A B F \<and> bet P E G \<and> bet Q F G \<and> \<not> col A B P \<and> \<not> col A B Q` by blast
	have "\<not> col A B Q" using `col A B E \<and> col A B F \<and> bet P E G \<and> bet Q F G \<and> \<not> col A B P \<and> \<not> col A B Q` by blast
	have "same_side Q P A B" using sameside_b[OF `col A B F` `col A B E` `bet Q F G` `bet P E G` `\<not> col A B Q` `\<not> col A B P`] .
	have "col B A E" using collinearorder[OF `col A B E`] by blast
	have "col B A F" using collinearorder[OF `col A B F`] by blast
	have "\<not> col B A P" using NCorder[OF `\<not> col A B P`] by blast
	have "\<not> col B A Q" using NCorder[OF `\<not> col A B Q`] by blast
	have "same_side P Q B A" using sameside_b[OF `col B A E` `col B A F` `bet P E G` `bet Q F G` `\<not> col B A P` `\<not> col B A Q`] .
	have "same_side Q P B A" using sameside_b[OF `col B A F` `col B A E` `bet Q F G` `bet P E G` `\<not> col B A Q` `\<not> col B A P`] .
	have "same_side Q P A B \<and> same_side P Q B A \<and> same_side Q P B A" using `same_side Q P A B` `same_side P Q B A` `same_side Q P B A` by blast
	thus ?thesis by blast
qed

end