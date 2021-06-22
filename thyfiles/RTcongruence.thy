theory RTcongruence
	imports Axioms Definitions Theorems
begin

theorem RTcongruence:
	assumes: `axioms`
		"ang_suppl A B C D E F"
		"ang_eq A B C P Q R"
	shows: "ang_suppl P Q R D E F"
proof -
	obtain a b c d e where "linear_pair a b c d e \<and> ang_eq A B C a b c \<and> ang_eq D E F d b e" sorry
	have "linear_pair a b c d e" using `linear_pair a b c d e \<and> ang_eq A B C a b c \<and> ang_eq D E F d b e` by blast
	have "ang_eq A B C a b c" using `linear_pair a b c d e \<and> ang_eq A B C a b c \<and> ang_eq D E F d b e` by blast
	have "ang_eq D E F d b e" using `linear_pair a b c d e \<and> ang_eq A B C a b c \<and> ang_eq D E F d b e` by blast
	have "ang_eq P Q R A B C" using equalanglessymmetric[OF `axioms` `ang_eq A B C P Q R`] .
	have "ang_eq P Q R a b c" using equalanglestransitive[OF `axioms` `ang_eq P Q R A B C` `ang_eq A B C a b c`] .
	have "linear_pair a b c d e \<and> ang_eq P Q R a b c \<and> ang_eq D E F d b e" using `linear_pair a b c d e \<and> ang_eq A B C a b c \<and> ang_eq D E F d b e` `ang_eq P Q R a b c` `linear_pair a b c d e \<and> ang_eq A B C a b c \<and> ang_eq D E F d b e` by blast
	have "ang_suppl P Q R D E F" sorry
	thus ?thesis by blast
qed

end