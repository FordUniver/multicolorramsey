---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults

# layout: home
usemathjax: true
---

The purpose of this repository is to hold a LEAN4 formalization of [Upper bounds for multicolour Ramsey numbers](https://arxiv.org/abs/2410.17197) by Balister et al. (2024). The following people is an alphabetical list of contributors:

* [Yamaan Attwa](https://www.math-berlin.de/about-bms/life-at-bms/life-at-bms/yamaan-from-syria)
* [Aldo Kiem](https://iol.zib.de/team/aldo-kiem.html)
* [Olivia Röhrig](https://iol.zib.de/team/olivia-roehrig.html)
* [Christoph Spiegel](https://iol.zib.de/team/christoph-spiegel.html)

## 🔗 Mathlib Contributions

{% assign data = site.data.mathlib_contributions %}

This project has contributed **{{ data.summary.merged | default: 0 }}** merged PRs to Mathlib.

{% for contrib in data.contributions %}
- **{{ contrib.name }}** ([PR #{{ contrib.pr_number }}]({{ contrib.pr_url }}))
  {% if contrib.status == "merged" %}✅ Merged{% endif %} {% if contrib.merged_date %}on {{ contrib.merged_date }}{% endif %}
  *{{ contrib.description | strip }}*
{% endfor %}