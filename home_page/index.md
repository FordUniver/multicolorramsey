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

## Mathlib PRs

{% assign contributions = site.data.mathlib_contributions.contributions %}
{% assign merged_count = contributions | where: "status", "merged" | size %}
{% assign cleaned_count = contributions | where: "status", "cleaned" | size %}
{% assign submitted_count = contributions | where: "status", "submitted" | size %}
{% assign ready_count = contributions | where: "status", "ready_to_submit" | size %}
{% assign branch_count = contributions | where: "status", "branch_created" | size %}
{% assign tentative_count = contributions | where: "status", "tentative" | size %}
{% assign in_progress = submitted_count | plus: ready_count | plus: branch_count | plus: tentative_count %}
{% assign total_merged = merged_count | plus: cleaned_count %}

This project has contributed **{{ total_merged }}** merged PRs to Mathlib{% if in_progress > 0 %}, with **{{ in_progress }}** in progress{% endif %}.

<table>
  <thead>
    <tr>
      <th>Name</th>
      <th>Stage</th>
      <th>Target File</th>
      <th>PR/Details</th>
    </tr>
  </thead>
  <tbody>
{% for contrib in contributions %}
    <tr>
      <td><strong>{{ contrib.name }}</strong><br/>
          <small style="color: #666;">{{ contrib.description | strip | truncatewords: 20 }}</small></td>
      <td>
        {% if contrib.status == "cleaned" %}
          <span style="color: #888;">✓ Cleaned</span>
        {% elsif contrib.status == "merged" %}
          <span style="color: #28a745;">✓ Merged</span>
        {% elsif contrib.status == "submitted" %}
          <span style="color: #0366d6;">⟳ Submitted</span>
        {% elsif contrib.status == "ready_to_submit" %}
          <span style="color: #6f42c1;">→ Ready</span>
        {% elsif contrib.status == "branch_created" %}
          <span style="color: #f9826c;">◐ Branch</span>
        {% elsif contrib.status == "tentative" %}
          <span style="color: #959da5;">○ Tentative</span>
        {% else %}
          <span>{{ contrib.status }}</span>
        {% endif %}
      </td>
      <td><code style="font-size: 0.85em;">{{ contrib.target_file }}</code></td>
      <td>
        {% if contrib.pr_number %}
          <a href="{{ contrib.pr_url }}">#{{ contrib.pr_number }}</a>
          {% if contrib.merged_date %}<br/><small>{{ contrib.merged_date }}</small>{% endif %}
        {% elsif contrib.branch_name %}
          <small>Branch: <code>{{ contrib.branch_name }}</code></small>
        {% else %}
          <small style="color: #666;">—</small>
        {% endif %}
      </td>
    </tr>
{% endfor %}
  </tbody>
</table>

### Stage Legend
- **○ Tentative**: Code moved to ToMathlib folder
- **◐ Branch**: Isolated on feature branch
- **→ Ready**: Finalized and ready for submission
- **⟳ Submitted**: PR created on mathlib
- **✓ Merged**: PR merged to mathlib
- **✓ Cleaned**: Code removed from this project
