#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <assert.h>

struct image {
  int larg;
  int haut;
  int maxc;
  uint16_t **pixels;
};

typedef struct image image;

/** Fabrique une image à partir du contenu d'un fichier supposé au
    format PGM ASCII */
image *charger_image(char *nom_fichier) {

  FILE *fichier = fopen(nom_fichier, "r");
  if (fichier == NULL) {
    return NULL;
  }

  // Vérifie que le format commence bien par P2
  char c = '\0';
  fscanf(fichier, "%c", &c);
  assert(c == 'P');
  fscanf(fichier, "%c", &c);
  assert(c == '2');

  image *img = malloc(sizeof(image));

  fscanf(fichier, "%d", &img->larg);
  fscanf(fichier, "%d", &img->haut);
  fscanf(fichier, "%d", &img->maxc);

  img->pixels = malloc(img->haut * sizeof(uint16_t*));
  for (int i = 0; i < img->haut; i++) {
    img->pixels[i] = malloc(img->larg * sizeof(uint16_t));
    for (int j = 0; j < img->larg; j++) {
      int p = 0;
      fscanf(fichier, "%d", &p);
      assert(0 <= p && p <= 65536);
      img->pixels[i][j] = (uint16_t)p;
    }
  }
  fclose(fichier);

  return img;

}

/** Renvoie le caractère caché dans les `8` premières cases d'un
    tableau supposé de longueur au moins `8` */
char caractere(uint16_t *tab) {
  int res = 0;
  for (int j = 0; j < 8; j++) {
    res *= 2;
    res += tab[j] % 2;
  }
  return (char)res;
}

/** Écrit dans le flux le message caché dans l'image. On suppose que
    l'image, et le flux sont valides, et en particulier non `NULL`. On
    suppose également que le message est valide et donc, en
    particuler, que `img->larg >= 8`. */
int sauvegarder_message(image *img, char *nom_sortie) {
  FILE *sortie = fopen(nom_sortie, "w");
  if (sortie == NULL) {
    fprintf(stderr, "Impossible d'ouvrir le fichier %s en écriture\n", nom_sortie);
    return 1;
  }
  for (int i = 0; i < img->haut; i++) {
    char c = caractere(img->pixels[i]);
    if (c == '\0') {
      break;
    }
    fprintf(sortie, "%c", c);
  }
  fclose(sortie);
  return 0;
}

/** Insère le caractère dans les `8` premières cases du tableau. On
    suppose que le tableau est de taille suffisante. */
void inserer_caractere(char c, uint16_t *tab) {
  int n = (int)c;
  for (int j = 7; j >= 0; j--) {
    tab[j] = 2 * (tab[j] / 2) + n % 2;
    n /= 2;
  }
}

/** Cache un message dans une image. On suppose que l'image est de
    hauteur et de largeur suffisante. */
int cacher(image *img, char *nom_entree) {
  FILE *entree = fopen(nom_entree, "r");
  if (entree == 0) {
    fprintf(stderr, "Impossible d'ouvrir le fichier %s en lecture\n", nom_entree);
    return 1;
  }
  assert(img->larg >= 8);
  int i = 0;
  while (!feof(entree)) {
    assert(i < img->haut);
    char c = '\0';
    fscanf(entree, "%c", &c);
    inserer_caractere(c, img->pixels[i]);
    i++;
  }
  fclose(entree);
  return 0;
}

/** Sauvegarde une image dans un fichier au format PGM ASCII. On
    suppose que l'image est valide. */
int sauvegarder_image(image *img, char *nom_fichier) {
  FILE *fichier = fopen(nom_fichier, "w");
  if (fichier == NULL) {
    fprintf(stderr, "Impossible d'ouvrir le fichier %s en écriture\n", nom_fichier);
    return 1;
  }
  fprintf(fichier, "P2\n");
  fprintf(fichier, "%d %d\n", img->larg, img->haut);
  fprintf(fichier, "%d\n", img->maxc);
  for (int i = 0; i < img->haut; i++) {
    for (int j = 0; j < img->larg; j++) {
      fprintf(fichier, "%d", (int)img->pixels[i][j]);
      fprintf(fichier, "%c", j < img->larg - 1 ? ' ' : '\n');
    }
  }
  return 0;
}

void liberer_image(image *img) {
  for (int i = 0; i < img->haut; i++) {
    free(img->pixels[i]);
  }
  free(img->pixels);
  free(img);
}

void masquer(image *dst, image *src) {
  assert(dst->larg == src->larg && dst->haut == src->haut && dst->maxc == src->maxc);
  const uint16_t mask = 0xFF00;
  for (int i = 0; i < src->haut; i++) {
    for (int j = 0; j < src->larg; j++) {
      dst->pixels[i][j] &= mask;
      dst->pixels[i][j] += ~mask & (src->pixels[i][j] >> 8);
    }
  }
}

void demasquer(image *img) {
  for (int i = 0; i < img->haut; i++) {
    for (int j = 0; j < img->larg; j++) {
      img->pixels[i][j] <<= 8;
    }
  }
}

int main(int argc, char* argv[]) {
  image *i1 = charger_image("quelle-est-la-meilleure-equipe-de-go.pgm");
  demasquer(i1);
  sauvegarder_image(i1, "kiki.pgm");

}