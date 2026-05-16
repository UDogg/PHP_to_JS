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
        Schema::table('template_master', function (Blueprint $table) {
            if (!Schema::hasColumn('template_master', 'subject')) {
                $table->string('subject');
            }
            if (!Schema::hasColumn('template_master', 'to')) {
                $table->string('to');
            }
            if (!Schema::hasColumn('template_master', 'bcc')) {
                $table->string('bcc');
            }
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('template_master', function (Blueprint $table) {
            $table->string('subject');
            $table->string('to');
            $table->string('bcc');
        });
    }
};
