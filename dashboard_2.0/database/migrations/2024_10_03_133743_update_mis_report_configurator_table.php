<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

class UpdateMisReportConfiguratorTable extends Migration
{
    public function up()
    {
        // Drop the table if it exists
        Schema::dropIfExists('mis_report_configurator');

        // Recreate the table with the new schema
        Schema::create('mis_report_configurator', function (Blueprint $table) {
            $table->id('mis_report_configurator_id')->autoIncrement();
            $table->string('lob_id')->nullable();
            $table->string('role_id')->nullable();
            $table->string('status_id')->nullable();
            $table->string('template_name', 255)->nullable();
            $table->enum('status', ['Y', 'N'])->default('Y');
            $table->timestamp('created_at')->nullable();
            $table->timestamp('updated_at')->nullable();
            $table->timestamp('deleted_at')->nullable();
            $table->unsignedBigInteger('user_type_id')->nullable();
            $table->string('column_name', 255)->nullable();
            $table->string('sequence', 255)->nullable();
            $table->unsignedBigInteger('user_id')->nullable();
            $table->string('user_type', 255)->nullable();
            $table->string('stage_name', 255)->nullable();
            $table->string('stage_id')->nullable();
            $table->longText('columns')->nullable();  // Assuming `columns` is a JSON field
            $table->string('static_columns', 255)->nullable();
        });
    }

    public function down()
    {
        // Rollback by dropping the table if it exists
        Schema::dropIfExists('mis_report_configurator');
    }
}
