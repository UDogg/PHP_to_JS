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
        Schema::table('employee_payroll_id', function (Blueprint $table) {
        $table->string('ANA_RM_ID')->nullable()->after('employee_type');
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('employee_payroll_id', function (Blueprint $table) {
            $table->dropColumn('ANA_RM_ID');
        });
    }
};
