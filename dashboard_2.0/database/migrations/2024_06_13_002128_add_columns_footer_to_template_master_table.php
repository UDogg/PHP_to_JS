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
            $table->string('footer')->nullable();
            $table->string('global_header')->nullable();
            $table->string('message_type')->nullable();
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('template_master', function (Blueprint $table) {
            $table->dropColumn('footer');
            $table->dropColumn('global_header');
            $table->dropColumn('message_type');
        });
    }
};
