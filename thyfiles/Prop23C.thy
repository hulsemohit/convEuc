theory Prop23C
	imports Geometry Prop23B betweennotequal collinear4 collinearorder equalitysymmetric inequalitysymmetric
begin

theorem(in euclidean_geometry) Prop23C:
	assumes 
		"A \<noteq> B"
		"\<not> col D C E"
		"\<not> col A B P"
	shows "\<exists> F G. ray_on A B G \<and> ang_eq F A G D C E \<and> same_side F P A B"
proof -
	have "\<not> (P = A)"
	proof (rule ccontr)
		assume "\<not> (P \<noteq> A)"
		hence "P = A" by blast
		have "A = P" using equalitysymmetric[OF `P = A`] .
		have "col A B P" using collinear_b `A = P` by blast
		show "False" using `col A B P` `\<not> col A B P` by blast
	qed
	hence "P \<noteq> A" by blast
	obtain Q where "bet P A Q \<and> seg_eq A Q P A" using extensionE[OF `P \<noteq> A` `P \<noteq> A`]  by  blast
	have "bet P A Q" using `bet P A Q \<and> seg_eq A Q P A` by blast
	have "A = A" using equalityreflexiveE.
	have "col A B A" using collinear_b `A = A` by blast
	have "\<not> (col A B Q)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col A B Q))"
hence "col A B Q" by blast
		have "col P A Q" using collinear_b `bet P A Q \<and> seg_eq A Q P A` by blast
		have "col Q A B" using collinearorder[OF `col A B Q`] by blast
		have "col Q A P" using collinearorder[OF `col P A Q`] by blast
		have "A \<noteq> Q" using betweennotequal[OF `bet P A Q`] by blast
		have "Q \<noteq> A" using inequalitysymmetric[OF `A \<noteq> Q`] .
		have "col A B P" using collinear4[OF `col Q A B` `col Q A P` `Q \<noteq> A`] .
		have "\<not> col A B P" using `\<not> col A B P` .
		show "False" using `\<not> col A B P` `col A B P` by blast
	qed
	hence "\<not> col A B Q" by blast
	obtain F G where "ray_on A B G \<and> ang_eq F A G D C E \<and> oppo_side F A B Q" using Prop23B[OF `A \<noteq> B` `\<not> col D C E` `\<not> col A B Q`]  by  blast
	have "ray_on A B G" using `ray_on A B G \<and> ang_eq F A G D C E \<and> oppo_side F A B Q` by blast
	have "ang_eq F A G D C E" using `ray_on A B G \<and> ang_eq F A G D C E \<and> oppo_side F A B Q` by blast
	have "oppo_side F A B Q" using `ray_on A B G \<and> ang_eq F A G D C E \<and> oppo_side F A B Q` by blast
	obtain J where "bet F J Q \<and> col A B J \<and> \<not> col A B F" using oppositeside_f[OF `oppo_side F A B Q`]  by  blast
	have "bet F J Q" using `bet F J Q \<and> col A B J \<and> \<not> col A B F` by blast
	have "col A B J" using `bet F J Q \<and> col A B J \<and> \<not> col A B F` by blast
	have "\<not> col A B F" using `bet F J Q \<and> col A B J \<and> \<not> col A B F` by blast
	have "bet P A Q" using `bet P A Q` .
	have "same_side F P A B" using sameside_b[OF `col A B J` `col A B A` `bet F J Q` `bet P A Q` `\<not> col A B F` `\<not> col A B P`] .
	have "ray_on A B G \<and> ang_eq F A G D C E \<and> same_side F P A B" using `ray_on A B G \<and> ang_eq F A G D C E \<and> oppo_side F A B Q` `ray_on A B G \<and> ang_eq F A G D C E \<and> oppo_side F A B Q` `same_side F P A B` by blast
	thus ?thesis by blast
qed

end