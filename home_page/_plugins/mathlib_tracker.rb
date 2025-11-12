# frozen_string_literal: true

require 'yaml'

module Jekyll
  # Generator plugin to collect Mathlib contributions and create data file
  class MathlibTracker < Generator
    safe true
    priority :high

    def generate(site)
      Jekyll.logger.info 'MathlibTracker:', 'Collecting contributions...'

      # Path to ToMathlib directory relative to site root
      tomathlib_path = File.join(site.source, '..', 'ToMathlib')

      unless Dir.exist?(tomathlib_path)
        Jekyll.logger.warn 'MathlibTracker:', "ToMathlib directory not found at #{tomathlib_path}"
        return
      end

      contributions = collect_contributions(tomathlib_path)

      # Sort contributions by status and date
      # Order: cleaned (oldest first), merged (oldest first), submitted, ready_to_submit, branch_created, tentative
      status_order = {
        'cleaned' => 0,
        'merged' => 1,
        'submitted' => 2,
        'ready_to_submit' => 3,
        'branch_created' => 4,
        'tentative' => 5
      }
      contributions.sort_by! do |c|
        status = c['status'] || 'tentative'
        date = c['merged_date']&.to_s || c['created_date']&.to_s || ''
        [
          status_order.fetch(status, 99),
          date  # Ascending order (oldest first for cleaned/merged)
        ]
      end

      # Create data structure (no summary needed, calculated in template)
      data = {
        'contributions' => contributions
      }

      # Write to _data directory
      data_dir = File.join(site.source, '_data')
      FileUtils.mkdir_p(data_dir)
      data_file = File.join(data_dir, 'mathlib_contributions.yaml')

      File.write(data_file, YAML.dump(data))

      Jekyll.logger.info 'MathlibTracker:', "Generated #{data_file}"
      Jekyll.logger.info 'MathlibTracker:', "Total contributions: #{contributions.size}"
    end

    private

    def collect_contributions(tomathlib_path)
      contributions = []

      Dir.glob(File.join(tomathlib_path, '*')).each do |subdir|
        next unless File.directory?(subdir)

        metadata_file = File.join(subdir, 'metadata.yaml')
        unless File.exist?(metadata_file)
          Jekyll.logger.warn 'MathlibTracker:', "#{File.basename(subdir)} missing metadata.yaml"
          next
        end

        begin
          metadata = YAML.load_file(metadata_file)
          contributions << metadata
        rescue => e
          Jekyll.logger.error 'MathlibTracker:', "Error reading #{metadata_file}: #{e.message}"
        end
      end

      contributions
    end
  end
end
