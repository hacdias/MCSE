import svgwrite
import json
import matplotlib as mpl
import matplotlib.cm as cm
import matplotlib

year = 1958

def getColor (temp):
  norm = mpl.colors.Normalize(vmin=-10, vmax=30)
  cmap = cm.heat
  m = cm.ScalarMappable(norm=norm, cmap=cmap)
  rgb = m.to_rgba(temp)
  return matplotlib.colors.rgb2hex(rgb)

with open(f'{year}.json') as json_file:
  data = json.load(json_file)
  if len(data) != 12:
    print('invalid number of months')
    exit(1)

  for i in range(0, 12):
    dwg = svgwrite.Drawing(f'{year}-{i+1}.svg', profile='tiny')
    x, y = 0, 0
    for lat in data[i]:
      if lat is not None:
        for temp in lat:
          if temp is not None:
            dwg.add(dwg.rect((x, y), (1, 1), fill=getColor(temp)))
          x += 1
      x = 0
      y += 1
    dwg.save()
  


