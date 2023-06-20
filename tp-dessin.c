{
    "cells" : [],
              "metadata" : {},
                           "nbformat" : 4,
                           "nbformat_minor" : 4
}

int red[3] = {255, 0, 0}; // red est un tableau de trois int

typedef int rgb[3]; // rgb est le *type* « tableau de trois int »

rgb red = {255, 0, 0};
rgb green = {0, 255, 0};
rgb blue = {0, 0, 255};
rgb black = {0, 0, 0};
rgb white = {255, 255, 255};

const int height = 600;
const int width = 800;
rgb canvas[600][800];

#define HEIGHT 600
#define WIDTH 800
rgb canvas[HEIGHT][WIDTH];

void put_pixel(int x, int y, rgb c)

    // fonction print_canvas doit afficher sur la sortie standard (à l’aide de la fonction printf) le contenu d’un fichier PPM correspondant au tableau canvas.

    void print_canvas(void)
{
    printf("P3\n");
    printf("%d %d\n", WIDTH, HEIGHT);
    printf("255\n");
    for (int i = 0; i < HEIGHT; i++)
    {
        for (int j = 0; j < WIDTH; j++)
        {
            for (int k = 0; k < 3; k++)
            {
                printf("%d ", canvas[i][j][k]);
            }
            printf("\n");
        }
    }
}

// fonction permettant de tracer une ligne horizontale. Cette fonction prendra en entrée une ordonnée, deux abscisses et une couleur.

void draw_h_line(int y, int x0, int x1, rgb c)
{
    if (x0 > x1)
    {
        draw_h_line(y, x1, x0, c);
        return;
    }
    for (int x = x0; x <= x1; x++)
    {
        put_pixel(x, y, c);
    }
}

// même fonction pour tracer une ligne verticale.

void draw_v_line(int x, int y_start, int y_end, rgb c)
{
    if (y_start > y_end)
    {
        draw_v_line(x, y_end, y_start, c);
        return;
    }
    for (int y = y_start; y <= y_end; y++)
    {
        put_pixel(x, y, c);
    }
}

/*fonction permettant de tracer un rectangle aligné avec les axes (deux côtés
verticaux et deux côtés horizontaux). Le rectangle sera spécifié par la donnée de deux
coins opposés (ainsi que par une couleur)*/

void draw_rectangle(int x0, int y0, int x1, int y1, rgb c)
{
    draw_h_line(y0, x0, x1, c);
    draw_h_line(y1, x0, x1, c);
    draw_v_line(x0, y0, y1, c);
    draw_v_line(x1, y0, y1, c);
}

/*fonction permettant de « remplir » un rectangle du même type qu’à la question
précédente*/

void fill_rectangle(int x0, int y0, int x1, int y1, rgb c)
{
    if (y0 > y1)
    {
        fill_rectangle(x1, y1, x0, y0, c);
    }
    else
    {
        for (int y = y0; y <= y1; y++)
        {
            draw_h_line(y, x0, x1, c);
        }
    }
}

int distance_squared(int x0, int y0, int x1, int y1)
{
    int dx = x1 - x0;
    int dy = y1 - y0;
    return dx * dx + dy * dy;
}

/*fonction permettant de remplir un disque spécifié par son centre et son rayon.*/

void fill_disk(int xc, int yc, int r, rgb c)
{
    int xmin = xc - r;
    int xmax = xc + r;
    int ymin = yc - r;
    int ymax = yc + r;
    for (int x = xmin; x <= xmax; x++)
    {
        for (int y = ymin; y <= ymax; y++)
        {
            if (distance_squared(xc, yc, x, y) <= r * r)
            {
                put_pixel(x, y, c);
            }
        }
    }
}

/*fonction clamp définie par 0 si x<0 255 si x>255 x sinon*/

int clamp(double x)
{
    if (x < 0.)
        return 0;
    if (x > 255.)
        return 255;
    return (int)x;
}

void mix(rgb c0, rgb c1, double alpha, double beta, rgb result)
{
    for (int k = 0; k < 3; k++)
    {
        result[k] = clamp(alpha * c0[k] + beta * c1[k]);
    }
}

/*Cette fonction tracera une ligne horizontale, avec le point d’abscisse x0 de couleur c0,
le point d’abscisse x1 de couleur c1, et les points intermédiaires coloriés grâce à une
interpolation linéaire de ces deux couleurs.*/

void draw_h_gradient(int y, int x0, int x1, rgb c0, rgb c1)
{
    if (x0 > x1)
    {
        draw_h_gradient(y, x1, x0, c1, c0);
        return;
    }
    for (int x = x0; x <= x1; x++)
    {
        double ratio = (double)(x - x0) / (double)(x1 - x0);
        rgb c; // non initalisé pour l'instant
        mix(c0, c1, 1.0 - ratio, ratio, c);
        // c a désormais un contenu bien défini
        put_pixel(x, y, c);
    }
}

void fill_disk_gradient(int xc, int yc, int r, rgb c_center, rgb c_edge)
{
    int xmin = xc - r;
    int xmax = xc + r;
    int ymin = yc - r;
    int ymax = yc + r;
    for (int x = xmin; x <= xmax; x++)
    {
        for (int y = ymin; y <= ymax; y++)
        {
            double ratio = sqrt(distance_squared(xc, yc, x, y)) / r;
            if (ratio <= 1.)
            {
                rgb c;
                mix(c_center, c_edge, 1.0 - ratio, ratio, c);
                put_pixel(x, y, c);
            }
        }
    }
}

/*fonction get_pixel qui remplit le tableau result avec le contenu de la case de
canvas correspondant aux coordonnées (x, y) (on s’inspirera de put_pixel, et on ne fera
rien dans le cas où les coordonnées données sont hors-cadre).*/

void get_pixel(int x, int y, rgb result)
{
    int i = HEIGHT - 1 - y;
    int j = x;
    if (i < 0 || i >= HEIGHT || j < 0 || j > WIDTH)
        return;
    for (int k = 0; k < 3; k++)
    {
        result[k] = canvas[i][j][k];
    }
}

/*fonction mix_pixel qui remplace le pixel de coordonnées (x, y) par le mélange
de sa valeur actuelle (avec coefficient β) et de la couleur c fournie (avec coefficient α).*/

void mix_pixel(int x, int y, double alpha, double beta, rgb c)
{
    rgb c0;
    get_pixel(x, y, c0);
    mix(c, c0, alpha, beta, c0);
    put_pixel(x, y, c0);
}

/* fonction add_disk permettant d’obtenir facilement un dessin*/

void add_disk(int xc, int yc, int r, rgb c)
{
    int xmin = xc - r;
    int xmax = xc + r;
    int ymin = yc - r;
    int ymax = yc + r;
    for (int x = xmin; x <= xmax; x++)
    {
        for (int y = ymin; y <= ymax; y++)
        {
            if (distance_squared(xc, yc, x, y) <= r * r)
            {
                mix_pixel(x, y, 1., 1., c);
            }
        }
    }
}

double x = 3.76;
double x_rounded = round(x) // x_rounded vaut 4.0
    int n = x_rounded       // n vaut 4

    // Ou en une seule étape :
    int n = round(3.76) // n vaut 4

    /*onction utilisant cet algorithme pour tracer une ligne de pente comprise entre
    0 et 1*/

    void
    draw_line(int x0, int y0, int x1, int y1, rgb c)
{
    if (x0 == x1)
    {
        // pente non définie
        draw_v_line(x0, y0, y1, c);
        return;
    }
    bool steep = abs(y1 - y0) > abs(x1 - x0);
    double m = (double)(y1 - y0) / (x1 - x0);
    if (!steep)
    {
        // valeur absolue de la pente inférieure à 1
        if (x0 > x1)
        {
            draw_line(x1, y1, x0, y0, c);
            return;
        }
        for (int x = x0; x <= x1; x++)
        {
            int y = round(y0 + m * (x - x0));
            put_pixel(x, y, c);
        }
    }
    else
    {
        // valeur absolue de la pente supérieure à 1
        if (y0 > y1)
        {
            draw_line(x1, y1, x0, y0, c);
            return;
        }
        for (int y = y0; y <= y1; y++)
        {
            int x = round(x0 + (y - y0) / m);
            put_pixel(x, y, c);
        }
    }
}

/*Cette fonction tracera nb_spokes rayons du cercle de centre (xc, yc) et de rayon radius. Le
premier de ces rayons sera horizontal et les autres seront régulièrement espacés en terme
d’angle*/

void draw_spokes(int xc, int yc, int r, int nb_spokes, rgb c_center)
{
    double pi = 3.1416;
    double angle = 2 * pi / nb_spokes;
    for (int i = 0; i < nb_spokes; i++)
    {
        double theta = i * angle;
        int x = round(xc + r * cos(theta));
        int y = round(yc + r * sin(theta));
        draw_line(xc, yc, x, y, c_center);
    }
}

void bresenham_low(int x0, int y0, int x1, int y1, rgb c)
{
    // Preconditions:
    // abs(y1 - y0) <= abs(x1 - x0) et x0 <= x1
    int dx = x1 - x0;
    int dy = y1 - y0;
    int y_increment = 1;
    if (dy < 0)
    {
        y_increment = -1;
        dy = -dy;
    }
    int err = dx - 2 * dy;
    int y = y0;
    for (int x = x0; x <= x1; x++)
    {
        put_pixel(x, y, c);
        if (err < 0)
        {
            y = y + y_increment;
            err = err + 2 * dx - 2 * dy;
        }
        else
        {
            err = err - 2 * dy;
        }
    }
}

void bresenham_high(int x0, int y0, int x1, int y1, rgb c)
{
    // Preconditions:
    // abs(x1 - x0) <= abs(y1 - y0)
    // y0 <= y1
    int dx = x1 - x0;
    int dy = y1 - y0;
    int x_increment = 1;
    if (dx < 0)
    {
        x_increment = -1;
        dx = -dx;
    }
    int err = dy - 2 * dx;
    int x = x0;
    for (int y = y0; y <= y1; y++)
    {
        put_pixel(x, y, c);
        if (err < 0)
        {
            x = x + x_increment;
            err = err + 2 * dy - 2 * dx;
        }
        else
        {
            err = err - 2 * dx;
        }
    }
}

void bresenham(int x0, int y0, int x1, int y1, rgb c)
{
    int dx = x1 - x0;
    int dy = y1 - y0;
    if (abs(dx) > abs(dy))
    {
        if (dx >= 0)
            bresenham_low(x0, y0, x1, y1, c);
        else
            bresenham_low(x1, y1, x0, y0, c);
    }
    else
    {
        if (dy >= 0)
            bresenham_high(x0, y0, x1, y1, c);
        else
            bresenham_high(x1, y1, x0, y0, c);
    }
}

void _draw_circle_points(int xc, int yc, int dx, int dy, rgb c)
{
    put_pixel(xc + dx, yc + dy, c);
    put_pixel(xc - dx, yc + dy, c);
    put_pixel(xc + dx, yc - dy, c);
    put_pixel(xc - dx, yc - dy, c);
    put_pixel(xc + dy, yc + dx, c);
    put_pixel(xc - dy, yc + dx, c);
    put_pixel(xc + dy, yc - dx, c);
    put_pixel(xc - dy, yc - dx, c);
}

void draw_circle(int xc, int yc, int r, rgb c)
{
    int dx = r;
    int dy = 0;
    _draw_circle_points(xc, yc, dx, dy, c);
    while (dx > dy)
    {
        dy++;
        int d2_above = dx * dx + dy * dy;
        int d2_diag = (dx - 1) * (dx - 1) + dy * dy;
        int err_above = abs(r * r - d2_above);
        int err_diag = abs(r * r - d2_diag);
        if (err_diag < err_above)
        {
            dx--;
        }
        _draw_circle_points(xc, yc, dx, dy, c);
    }
}

int main(void)
{
    for (int x = 0; x < WIDTH; x++)
    {
        for (int y = 0; y < HEIGHT; y++)
        {
            put_pixel(x, y, red);
        }
    }
    return 0;
}