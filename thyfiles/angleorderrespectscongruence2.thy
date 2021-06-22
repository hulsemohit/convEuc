theory angleorderrespectscongruence2
	imports Axioms Definitions Theorems
begin

theorem angleorderrespectscongruence2:
	assumes: `axioms`
		"ang_lt A B C D E F"
		"ang_eq a b c A B C"
	shows: "ang_lt a b c D E F"
proof -
	obtain P Q R where "bet P Q R \<and> ray_on E D P \<and> ray_on E F R \<and> ang_eq A B C D E Q" sorry
	have "bet P Q R" using `bet P Q R \<and> ray_on E D P \<and> ray_on E F R \<and> ang_eq A B C D E Q` by blast
	have "ray_on E D P" using `bet P Q R \<and> ray_on E D P \<and> ray_on E F R \<and> ang_eq A B C D E Q` by blast
	have "ray_on E F R" using `bet P Q R \<and> ray_on E D P \<and> ray_on E F R \<and> ang_eq A B C D E Q` by blast
	have "ang_eq A B C D E Q" using `bet P Q R \<and> ray_on E D P \<and> ray_on E F R \<and> ang_eq A B C D E Q` by blast
	have "ang_eq a b c D E Q" using equalanglestransitive[OF `axioms` `ang_eq a b c A B C` `ang_eq A B C D E Q`] .
	have "ang_lt a b c D E F" sorry
	thus ?thesis by blast
qed

end