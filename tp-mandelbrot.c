#include <stdio.h>
#include <assert.h>
#include <stdlib.h>

#define ROWS 800
#define COLS 800

int arr[ROWS][COLS];

double expo(double x, int n)
{
    double res = 1.0;
    for (int i = 0; i < n; i = i + 1)
    {
        res = res * x;
    }
    return res;
}

double f(double x, double y, int n)
{
    double xn = expo(x, n);
    double yn = expo(y, n);
    return xn + yn;
}

void f(int n, int *nmax)
{
    printf("Début de l'appel de f(%d, _)\n", n);
    printf("n = %d\n", n);
    printf("&n = %p\n", &n);
    printf("nmax = %p\n", nmax);
    printf("*nmax = %d\n", *nmax);
    printf("&nmax = %p\n", &nmax);
    if (n < *nmax)
        f(n + 1, nmax);
    printf("Fin de l'appel de f(%d, _)\n", n);
}

void incremente(int *p)
{
    *p = *p + 1;
}

int divergence(double xc, double yc, int itermax)
{
    double x = 0.;
    double y = 0.;
    int i = 0;
    while (x * x + y * y <= 4. && i <= itermax)
    {
        double tmp = x;
        x = x * x - y * y + xc;
        y = 2. * tmp * y + yc;
        i++;
    }
    return i;
}

/*prend en entrée un numéro de ligne ou de colonne dans le tableau arr et renvoyant la partie
réelle ou imaginaire du complexe correspondant à ce pixel*/

double re(int j, double xmin, double xmax)
{
    double ratio = (double)j / (COLS - 1);
    return xmin + ratio * (xmax - xmin);
}

double im(int i, double ymin, double ymax)
{
    double ratio = (double)i / (ROWS - 1);
    return ymax + ratio * (ymin - ymax);
}

/*emplit le tableau global arr avec les valeurs renvoyées par la fonction divergence pour
les différents pixels*/

void fill_tab(double xmin, double xmax, double ymin, double ymax, int itermax)
{
    for (int i = 0; i < ROWS; i++)
    {
        for (int j = 0; j < COLS; j++)
        {
            double x = re(j, xmin, xmax);
            double y = im(i, ymin, ymax);
            arr[i][j] = divergence(x, y, itermax);
        }
    }
}

/*fonction void print_pixel_bw(int i, int j, int itermax) qui affiche
255 255 255 \n ou 0 0 0 \n selon que le pixel (i, j) de l’image appartient ou non à
Mitermax.*/

void print_pixel_bw(int i, int j, int itermax)
{
    int c = 0;
    if (arr[i][j] > itermax)
    {
        c = 255;
    }
    for (int k = 0; k < 3; k++)
    {
        printf("%d ", c);
    }
    printf("\n");
}

/*fonction void print_tab(int itermax) qui affiche le fichier PPM correspon-
dant à l’image calculée*/

void print_tab(int itermax)
{
    printf("P3\n");
    printf("%d %d\n", COLS, ROWS);
    printf("255\n");
    for (int i = 0; i < ROWS; i++)
    {
        for (int j = 0; j < COLS; j++)
        {
            print_pixel_gs(i, j, itermax);
        }
    }
}

void print_pixel_gs(int i, int j, int itermax)
{
    int c = 255 * arr[i][j] / itermax;
    for (int k = 0; k < 3; k++)
    {
        printf("%d ", c);
    }
    printf("\n");
}

void fill_droite(void)
{
    for (int i = 0; i < N; i = i + H)
    {
        int j = min(i + H - 1, N - 1);
        droite[j] = arr[j];
        j--;
        for (; j >= i; j--)
        {
            droite[j] = max(arr[j], droite[j + 1]);
        }
    }
}

void fill_gauche(void)
{
    for (int i = 0; i < N; i = i + H)
    {
        gauche[i] = arr[i];
        for (int j = i + 1; j < min(i + H, N); j++)
        {
            gauche[j] = max(gauche[j - 1], arr[j]);
        }
    }
}

void f(void)
{
    fill_gauche();
    fill_droite();
    int i;
    for (i = 0; i + H - 1 < N; i++)
    {
        result[i] = max(droite[i], gauche[i + H - 1]);
    }
    for (; i < N; i++)
    {
        result[i] = droite[i];
    }
}

int main(int argc, char *argv[])
{
    double xmin = -2.;
    double xmax = 2.;
    double ymin = -2.;
    double ymax = 2.;
    int itermax = 20;
    if (argc >= 2)
    {
        itermax = atoi(argv[1]);
    }
    if (argc == 6)
    {
        xmin = atof(argv[2]);
        xmax = atof(argv[3]);
        ymin = atof(argv[4]);
        ymax = atof(argv[5]);
    }
    fill_tab(xmin, xmax, ymin, ymax, itermax);
    print_tab(itermax);
    return 0;
}