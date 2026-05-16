<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

return new class extends Migration
{
    /**
     * Run the migrations.
     */
    public function up(): void
    {
        Schema::table('mis_report_configurator', function (Blueprint $table) {
            $table->string('user_type_id')->nullable();
            $table->string('column_name');
            $table->string('sequence');
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('mis_report_configurator', function (Blueprint $table) {
            //
            $table->dropColumn('user_type_id');
            $table->dropColumn('column_name');
            $table->dropColumn('sequence');

        });
    }
};
