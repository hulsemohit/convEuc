theory oppositesideflip
	imports Geometry NCorder collinearorder
begin

theorem(in euclidean_geometry) oppositesideflip:
	assumes 
		"oppo_side P A B Q"
	shows "oppo_side P B A Q"
proof -
	obtain r where "bet P r Q \<and> col A B r \<and> \<not> col A B P" using oppositeside_f[OF `oppo_side P A B Q`]  by  blast
	have "bet P r Q" using `bet P r Q \<and> col A B r \<and> \<not> col A B P` by blast
	have "col A B r" using `bet P r Q \<and> col A B r \<and> \<not> col A B P` by blast
	have "\<not> col A B P" using `bet P r Q \<and> col A B r \<and> \<not> col A B P` by blast
	have "\<not> col B A P" using NCorder[OF `\<not> col A B P`] by blast
	have "col B A r" using collinearorder[OF `col A B r`] by blast
	have "oppo_side P B A Q" using oppositeside_b[OF `bet P r Q` `col B A r` `\<not> col B A P`] .
	thus ?thesis by blast
qed

end