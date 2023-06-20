#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

#include "dicts.h"

struct TTT {
    int n;
    int k;
    int* grille;
};

typedef struct TTT ttt;

/*e fonction ttt* init_jeu(int n, int k) qui initialise un jeu de ttt(k, n) avec
une grille vide (donc ne contenant que des zéros)*/

ttt* init_jeu(int k, int n){
    ttt* jeu = malloc(sizeof(*jeu));
    int* grille = malloc((n * n) * sizeof(*grille));
    for (int i = 0; i < n * n; i++){
        grille[i] = 0;
    }
    jeu->k = k;
    jeu->n = n;
    jeu->grille = grille;
    return jeu;
}

/* fonction void liberer_jeu(ttt* jeu) qui libère l’espace mémoire occupé par
un jeu.*/

void liberer_jeu(ttt* jeu){
    free(jeu->grille);
    free(jeu);
}

/*e fonction int* repartition(ttt* jeu) qui renvoie un tableau de taille 3 correspondant à la répartition des cases dans le jeu : tab[i] correspond au nombre d’occurrences
de la valeur i dans la grille. La fonction renverra une erreur si la grille contient des numéros
autres que 0, 1 ou 2.
*/

int* repartition(ttt* jeu){
    int* repart = malloc(3 * sizeof(*repart));
    for (int i = 0; i < 3; i++) repart[i] = 0;
    for (int i = 0; i < jeu->n * jeu->n; i++){
        int val = jeu->grille[i];
        assert (0 <= val && val < 3);
        repart[val] += 1;
    }
    return repart;
}

/*fonction int joueur_courant(ttt* jeu) qui renvoie le numéro du joueur
dont c’est le tour (en supposant que c’est toujours le joueur 1 qui commence). La fonction
renverra 0 si toutes les cases de la grille sont remplies.*/

int joueur_courant(ttt* jeu){
    int* repart = repartition(jeu);

    int res;
    if (repart[0] == 0) res = 0;
    else if (repart[1] == repart[2]) res = 1;
    else res = 2;

    free(repart);
    return res;
}

/*fonction void jouer_coup(ttt* jeu, int lgn, int cln) qui joue un coup
pour le joueur courant dans la grille à une ligne et une colonne données. La fonction devra
afficher un message d’erreur et ne rien faire si la case correspondante ne contient pas 0.
On fera la conversion entre un couple d’indices de ligne et de colonne et l’indice de la case
dans le tableau unidimensionnel.
*/

void jouer_coup(ttt* jeu, int cln, int lgn){
    int i = lgn * jeu->n + cln;
    if (jeu->grille[i] != 0){
        printf("Coup impossible\n");
    } else {
        jeu->grille[i] = joueur_courant(jeu);
    }
}

/* fonction bool alignement(ttt* jeu, int i, int di, int joueur) qui prend
en argument un jeu, un indice de départ, une direction et un joueur et indique s’il existe
un alignement gagnant pour le joueur depuis la case de départ, dans la direction donnée.
On prendra garde, en gardant en mémoire la ligne et la colonne de la case courante, à ne
pas sortir de la grille.*/

bool alignement(ttt* jeu, int i, int di, int joueur){
    int k = jeu->k;
    int n = jeu->n;
    int cln = i % n;
    int lgn = i / n;
    int dc = ((di + 1) % n) - 1;
    int dl = (di + 1) / n;
    for (int j=0; j<k; j++){
        if (cln < 0 || cln >= n || lgn < 0 || lgn >= n){
            return false;
        }
        i = lgn * n + cln;
        if (jeu->grille[i] != joueur){
            return false;
        }
        cln += dc; lgn += dl;
    }
    return true;
}

/* fonction bool gagnant(ttt* jeu, int joueur) qui indique si un joueur
est gagnant ou non.*/

bool gagnant(ttt* jeu, int joueur){
    int n = jeu->n;
    int tabdi[4] = {1, n - 1, n, n + 1};
    for (int i = 0; i < n*n; i++){
        for (int j = 0; j < 4; j++){
            if (alignement(jeu, i, tabdi[j], joueur)){
                return true;
            }
        }
    }
    return false;
}

/*fonction int encodage(ttt* jeu) qui calcule un tel entier. On supposera qu’il
n’y a pas de dépassement d’entiers (on travaillera avec des petites grilles).
*/

int encodage(ttt* jeu){
    int cle = 0;
    int n = jeu->n;
    for (int i=0; i<n*n; i++){
        cle = 3 * cle + jeu->grille[i];
    }
    return cle;
}

/* fonction int attracteur(ttt* jeu, dict* d) qui prend en argument un jeu
et un dictionnaire et renvoie le numéro de l’attracteur auquel appartient la grille du jeu.
La fonction devra mémoriser le résultat dans le dictionnaire s’il n’y est pas déjà avant de
renvoyer la valeur. On considèrera qu’une position nulle est dans l’attracteur 0*/

int attracteur(ttt* jeu, dict* d){
    int cle = encodage(jeu);
    int n = jeu->n;
    int joueur = joueur_courant(jeu);
    if (!member(d, cle)){
        if (gagnant(jeu, joueur)) add(d, cle, joueur);
        else if (gagnant(jeu, 3 - joueur)) add(d, cle, 3 - joueur);
        else if (joueur == 0) add(d, cle, 0);
        else {
            int tab[3] = {0, 0, 0};
            for (int i=0; i<n*n; i++){
                if (jeu->grille[i] == 0){
                    jeu->grille[i] = joueur;
                    int att = attracteur(jeu, d);
                    jeu->grille[i] = 0;
                    tab[att] += 1;
                    if (att == joueur){
                        break;
                    }                                 
                }
            }
            if (tab[joueur] != 0) add(d, cle, joueur);
            else if (tab[0] != 0) add(d, cle, 0);
            else add(d, cle, 3 - joueur);
        }      
    }
    return get(d, cle);
}

/*fonction int strategie_optimale(ttt* jeu, dict* d) qui détermine
le coup optimal à jouer étant donné un jeu et un dictionnaire contenant des numéros
d’attracteurs.
*/

int strategie_optimale(ttt* jeu, dict* d){
    int att = attracteur(jeu, d);
    int n = jeu->n;
    int joueur = joueur_courant(jeu);
    for (int i=0; i<n*n; i++){
        if (jeu->grille[i] == 0){
            jeu->grille[i] = joueur;
            int att2 = attracteur(jeu, d);
            jeu->grille[i] = 0;
            if (att == att2){
                return i;
            }
        }
    }
    assert(false);
}

/*fonction void afficher(ttt* jeu) qui affiche le jeu en console. Voici par
exemple une manière d’afficher un jeu ttt(3, 4). On indiquera les numéros de lignes et
de colonnes.
*/

void afficher_ligne_sep(int n){
    printf("\n ");
    for (int i=0; i<n; i++){
        printf("+-");
    }
    printf("+\n");
}

void afficher(ttt* jeu){
    int n = jeu->n;
    char tab[3] = {' ', 'X', 'O'};
    printf(" ");
    for (int cln=0; cln<n; cln++){
        // affichage des numéros de colonnes
        printf(" %d", cln);
    }
    afficher_ligne_sep(n);
    for (int lgn=0; lgn<n; lgn++){
        printf("%d|", lgn);
        for (int cln=0; cln<n; cln++){
            int i = n * lgn + cln;
            printf("%c|", tab[jeu->grille[i]]);
        }
        afficher_ligne_sep(n);
    }
    printf("\n");
}

/*fonction void jouer_partie(int k, int n) qui crée une partie de ttt(k, n) et
permet de jouer contre l’ordinateur. La fonction devra :
■ demander si le joueur humain souhaite commencer ou non ;
■ demander à chaque coup du joueur humain la ligne et la colonne où il souhaite jouer ;
■ afficher la grille après chaque coup joué (par l’humain ou l’ordinateur) ;
■ arrêter la partie dès qu’un joueur a gagné ou quand la grille est pleine, et afficher le
joueur gagnant*/

void jouer_partie(int k, int n){
    ttt* jeu = init_jeu(k, n);
    char c;
    int IA, cln, lgn;
    while (true){
        printf("Voulez-vous commencer ? (o/n) ");
        scanf("%c", &c);
        if (c == 'o'){
            IA = 2;
            break;
        } else if (c == 'n'){
            IA = 1;
            break;
        }
    }
    dict* d = create();
    int joueur = 1;
    while (joueur != 0 && !gagnant(jeu, 1) && !gagnant(jeu, 2)){
        afficher(jeu);
        if (joueur == IA){
            int i = strategie_optimale(jeu, d);
            cln = i % n;
            lgn = i / n;
            printf("L'IA joue ligne %d, colonne %d\n", lgn, cln);
            jouer_coup(jeu, cln, lgn);
        } else {        
            printf("C'est a vous de jouer\n");
            printf("Saisir la ligne : ");
            scanf("%d", &lgn);
            printf("Saisir la colonne : ");
            scanf("%d", &cln);
            if (cln < 0 || cln >= jeu->n || lgn < 0 || lgn >= jeu->n){
                printf("Ces coordonnees ne sont pas possibles.\n");
            } else {
                jouer_coup(jeu, cln, lgn);
            }
        }
        joueur = joueur_courant(jeu);
    }
    afficher(jeu);
    if (gagnant(jeu, IA)){
        printf("L'IA a gagne !\n");
    } else if (gagnant(jeu, 3 - IA)){
        printf("Vous avez gagne !\n");
    } else {
        printf("C'est un match nul !\n");
    }
    liberer_jeu(jeu);
    dict_free(d);
}

int main(void){
    jouer_partie(4, 4);
    return 0;
}
